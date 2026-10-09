/* SPDX-License-Identifier: GPL-2.0 */
/*
 * lsm_hook.c - runtime LSM hook installation (ported from KernelSU/SukiSU hook/lsm_hook.c).
 * Both mechanisms write through ksu_patch_text(): every word they touch is read-only text, and the
 * replacement lives in module .text, so a patch has to go through stop_machine.
 *
 *   replace - overwrite the entry's function slot; the old pointer goes to hook->original
 *             for pass-through.  The slot is SELinux's, so a caller LSM returning non-zero
 *             first masks this hook.
 *   insert  - get in front of every registered LSM, so the hook can only ADD a denial:
 *               < 6.12   add our OWN security_hook_list node at the HEAD of the hlist
 *                        (hook->insert, KSU_LSM_HOOK_INSERT): no symbol, no original.
 *               >= 6.12  no hlist exists - dispatch is one static call per (hook, LSM
 *                        slot) - so insertion TAKES OVER SELinux's slot, whose original
 *                        must be called for pass-through (SUS_LSM_PASS_ORIG(), sus_path.c).
 */
#include <linux/compiler.h>
#include <linux/errno.h>
#include <linux/kernel.h>
#include <linux/lsm_hooks.h>
#include <linux/mutex.h>
#include <linux/delay.h>
#include <linux/rcupdate.h>
#include <linux/string.h>
#include <linux/version.h>		/* LINUX_VERSION_CODE for the gates below (do not rely on a transitive include) */

#include "symbol_resolver.h"
#include "lsm_hook.h"
#include "patch_memory.h"
#include "susfs_log.h"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
#include <linux/static_call.h>		/* __static_call_update() - EXPORT_SYMBOL_GPL */
#include <linux/static_call_types.h>	/* struct static_call_key */
#include <linux/lsm_count.h>		/* MAX_LSM_COUNT = the slots each hook has */
#include <linux/kallsyms.h>		/* KSYM_SYMBOL_LEN, to name the target function */
#include <linux/uaccess.h>		/* copy_from_kernel_nofault(), layout probe */
#endif

struct ksu_lsm_hook_entry {
    struct ksu_lsm_hook *hook;
};

/* Defined below; called from ksu_unregister_lsm_hook(). */
static void ksu_lsm_hook_drain(void);

static DEFINE_MUTEX(ksu_lsm_hook_lock);
static struct ksu_lsm_hook_entry ksu_lsm_hook_entries[16];
static int ksu_lsm_hook_count;

static bool ksu_lsm_hook_is_tracked(struct ksu_lsm_hook *hook)
{
    int i;

    for (i = 0; i < ksu_lsm_hook_count; i++) {
        if (ksu_lsm_hook_entries[i].hook == hook)
            return true;
    }

    return false;
}

static int ksu_lsm_hook_track(struct ksu_lsm_hook *hook)
{
    if (ksu_lsm_hook_is_tracked(hook))
        return 0;

    if (ksu_lsm_hook_count >= ARRAY_SIZE(ksu_lsm_hook_entries)) {
        pr_err("lsm_hook: tracking table full, cannot record %s\n", hook->head_name ?: "unknown");
        return -ENOSPC;
    }

    ksu_lsm_hook_entries[ksu_lsm_hook_count++].hook = hook;
    return 0;
}

static void ksu_lsm_hook_untrack(struct ksu_lsm_hook *hook)
{
    int i;

    for (i = 0; i < ksu_lsm_hook_count; i++) {
        if (ksu_lsm_hook_entries[i].hook != hook)
            continue;

        ksu_lsm_hook_entries[i] = ksu_lsm_hook_entries[--ksu_lsm_hook_count];
        return;
    }
}

static int ksu_lsm_hook_patch_slot(void **slot, void *value)
{
    void *patched = value;
    int ret;

    ret = ksu_patch_text(slot, &patched, sizeof(patched), KSU_PATCH_TEXT_FLUSH_DCACHE);
    if (!ret)
        smp_wmb();

    return ret;
}

#if LINUX_VERSION_CODE < KERNEL_VERSION(6, 12, 0)
/* ---- insertion into a hook list (hook->insert) -------------------------------
 * SELinux's node lives in selinux_hooks[] __lsm_ro_after_init, hence ksu_patch_text()
 * below; our node is writable and becomes reachable only once head->first is patched, so
 * no walk can observe a half-initialised node. */

/* Locate the list head for hook->head_name and cross-check it: the address is
 * offsetof(struct security_hook_heads, member), a __randomize_layout struct (RANDSTRUCT is off in
 * every GKI build this module targets), so LSM_HOOK_INIT's entry->head verifies that the first
 * entry at that address points back at it.  A wrong offset would otherwise patch an hlist_head no
 * call site walks - a hook silently never called, which reads like a working layer in every
 * counter - hence a mismatch fails the load, and an empty head is -ENOENT (as in replace). */
static int ksu_lsm_hook_head_at(unsigned long heads_addr, struct ksu_lsm_hook *hook,
                                struct hlist_head **out)
{
    struct hlist_head *head;
    struct security_hook_list *first;

    if (hook->head_offset + sizeof(struct hlist_head) > sizeof(struct security_hook_heads)) {
        pr_err("lsm_hook: %s: head offset %#lx is outside security_hook_heads\n",
                hook->head_name ?: "unknown", (unsigned long)hook->head_offset);
        return -EINVAL;
    }

    head = (struct hlist_head *)(heads_addr + hook->head_offset);
    first = hlist_entry_safe(READ_ONCE(head->first), struct security_hook_list, list);

    if (!first) {
        pr_err("lsm_hook: %s: hook list is empty - refusing to insert (nothing to cross-check the head offset against)\n",
                hook->head_name ?: "unknown");
        return -ENOENT;
    }
    if (first->head != head) {
        pr_err("lsm_hook: %s: entry at %px reports head %px, computed %px - struct security_hook_heads layout mismatch, refusing to patch\n",
                hook->head_name ?: "unknown", first, first->head, head);
        return -EINVAL;
    }

    *out = head;
    return 0;
}

/* Insert our node at the head of the list; lock held, head already validated. */
static int ksu_lsm_hook_insert_head(struct ksu_lsm_hook *hook, struct hlist_head *head)
{
    struct security_hook_list *node = &hook->list;
    struct hlist_node *first = READ_ONCE(head->first);
    struct security_hook_list *first_entry;
    int ret;

    first_entry = hlist_entry_safe(first, struct security_hook_list, list);
    if (!first_entry || first_entry->head != head) {
        pr_err("lsm_hook: %s: head %px changed under us, refusing to insert\n",
                hook->head_name ?: "unknown", head);
        return -EAGAIN;
    }

    /* Set the hook word through the offset the slot path uses (the per-hook initialiser
     * need not name the union member); `lsm` is char * on 5.10/5.15, const char * on 6.1. */
    memset(node, 0, sizeof(*node));
    *(void **)((char *)node + hook->hook_offset) = hook->replacement;
    node->head = head;
    node->lsm = "susfs";
    node->list.next = first;
    node->list.pprev = &head->first;

    /* 1. head->first, in __lsm_ro_after_init memory: this write publishes the node. */
    ret = ksu_lsm_hook_patch_slot((void **)&head->first, node);
    if (ret)
        return ret;

    /* 2. the displaced node's back pointer, inside selinux_hooks[] (also RO after init):
     *    a later removal of THAT node must not unlink from a stale pointer into ours. */
    ret = ksu_lsm_hook_patch_slot((void **)&first->pprev, &node->list.next);
    if (ret) {
        /* Roll back the publication - a wrong-way neighbour corrupts the list. */
        if (ksu_lsm_hook_patch_slot((void **)&head->first, first))
            pr_err("lsm_hook: %s: failed to roll back head->first after a failed insert\n",
                    hook->head_name ?: "unknown");
        node->list.next = NULL;
        node->list.pprev = NULL;
        return ret;
    }

    hook->entry = node;
    SUSFS_LOGI("lsm_hook: inserted %s as the first node of its list (head %px, before %px, replacement %px)\n",
            hook->head_name ?: "unknown", head, first, hook->replacement);
    return 0;
}

/* Unlink our node; the words it writes live in memory only ksu_patch_text() may touch. */
static int ksu_lsm_hook_remove_head(struct ksu_lsm_hook *hook)
{
    struct hlist_node **pprev = hook->list.list.pprev;
    struct hlist_node *next = READ_ONCE(hook->list.list.next);
    int ret;

    if (!pprev || READ_ONCE(*pprev) != &hook->list.list) {
        pr_err("lsm_hook: %s: back pointer %px does not point at our node - refusing to unlink\n",
                hook->head_name ?: "unknown", pprev);
        return -EINVAL;
    }

    ret = ksu_lsm_hook_patch_slot((void **)pprev, next);
    if (ret)
        return ret;

    /* 2. the successor's back pointer: not needed for the walk, but a later removal of
     *    THAT node must not write through a pointer into this module's memory. */
    if (next) {
        ret = ksu_lsm_hook_patch_slot((void **)&next->pprev, pprev);
        if (ret) {
            /* Our node is already out; re-link rather than leave a stale back pointer. */
            if (ksu_lsm_hook_patch_slot((void **)pprev, &hook->list.list))
                pr_err("lsm_hook: %s: failed to re-link our node after a failed unlink\n",
                        hook->head_name ?: "unknown");
            return ret;
        }
    }

    hook->list.list.next = NULL;
    hook->list.list.pprev = NULL;
    hook->entry = NULL;
    SUSFS_LOGI("lsm_hook: removed %s node from its list\n", hook->head_name ?: "unknown");
    return 0;
}
#endif /* < 6.12 */

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
typedef void (*ksu_static_call_update_t)(struct static_call_key *key, void *tramp, void *func);

static int ksu_lsm_hook_update_scall(struct lsm_static_call *scall, void *value)
{
    /* The generic arm of __static_call_update() is `WRITE_ONCE(key->func, func)` and cannot
     * fail - which is the arm these builds compile (the .ko imports neither __static_call_update
     * nor arch_static_call_transform), so the int return exists only for a tree whose config
     * selects the inline/arch arm, where the call can reject. Callers check it either way. */
    __static_call_update(scall->key, scall->trampoline, value);
    smp_wmb();
    return 0;
}

/* ---- insertion on >= 6.12: taking over SELinux's static-call slot ----------------
 *
 * 6.12 replaced the hlist dispatch with one static call per (hook, LSM slot), so there
 * is no list left to insert into: struct security_hook_list (include/linux/lsm_hooks.h)
 * lost its hlist node and its `lsm` field, and each (hook, LSM slot) is now a
 *   struct lsm_static_call { struct static_call_key *key; void *trampoline; struct
 *                            security_hook_list *hl; struct static_key_false *active; }
 * inside `extern struct lsm_static_calls_table static_calls_table __ro_after_init`.
 * security/security.c dispatches with
 *   if (static_branch_unlikely(&SECURITY_HOOK_ACTIVE_KEY(HOOK, NUM)))
 *       R = static_call(LSM_STATIC_CALL(HOOK, NUM))(...);
 * and lsm_static_call_init() filled each slot at boot: it walked hl->scalls, took the
 * first slot with !scall->hl, ran __static_call_update(scall->key, scall->trampoline,
 * hl->hook.lsm_func_addr), set scall->hl and enabled THAT slot's static key.
 *
 * An unregistered LSM cannot get a slot of its own (that needs static-key work this module
 * has no business doing), but it CAN take over a live one, and SELinux's is the right one:
 * its static key is already enabled, and it holds its documented position in the order, so
 * an earlier slot (capabilities) still runs first and later ones (safesetid, landlock,
 * bpf-lsm) still run whenever the hook's default is returned.  The displaced function is
 * called from the replacement (hook->original via SUS_LSM_PASS_ORIG()), so nothing SELinux
 * decided is lost - including the -ECHILD inode_permission's RCU walk depends on.  The only
 * symbol needed is static_calls_table; the write is the kernel's own __static_call_update().
 *
 * Which of linux/static_call.h's three definitions of __static_call_update() is compiled is decided by
 * CONFIG_HAVE_STATIC_CALL(_INLINE), NOT by the architecture; the extern one (kernel/static_call_inline.c)
 * needs HAVE_STATIC_CALL_INLINE, unset in every tree this module is built against.  Measured, not assumed:
 * the built android16-6.12 and android17-6.18 .ko files import neither __static_call_update nor
 * cpus_read_lock nor arch_static_call_transform(), i.e. the generic `WRITE_ONCE(key->func, func)` arm is
 * what got compiled - the same config that makes the trampoline those trees register NULL (security.c's
 * LSM_HOOK_TRAMP()).
 *
 * NOTHING IS WRITTEN until the slot passes all five validations below: the failure this must
 * not have is a jump target that is wrong rather than absent.  Every read uses
 * copy_from_kernel_nofault() - a bogus pointer cannot fault the check that exists to catch
 * it - and failing any of them returns without patching, so the hook is simply not armed
 * (-ENOSYS for every insert on this branch before the change) and an unknown layout costs
 * coverage, never a corrupted jump target:
 *   1. key/hl/trampoline are readable, key and hl are plausible kernel addresses, trampoline is
 *      NULL or one.  NULL is NOT a layout problem: security.c's LSM_HOOK_TRAMP() is NULL whenever
 *      the tree lacks CONFIG_HAVE_STATIC_CALL and lsm_static_call_init() hands that same NULL to
 *      __static_call_update() at boot (measured on both DDK trees this branch targets); either arm
 *      ends at key->func, which is what this code reads, saves and replaces;
 *   2. hl->scalls == &static_calls_table.<member>[0]: the entry is registered for THIS hook,
 *      which validates head_offset against the kernel's real layout - a RANDSTRUCT kernel
 *      (or any table whose member order moved) makes the two disagree;
 *   3. hl->lsmid->name reads as "selinux" - only SELinux's slot is ever taken;
 *   4. the slot's current target (key->func, what the dispatch calls) equals the entry's own
 *      hook word (hl + hook_offset): two places lsm_static_call_init() filled from one value;
 *   5. that target really is THIS hook's SELinux implementation: named through kallsyms as
 *      "selinux_<member>" (clone suffix allowed), exact match against the name-resolved symbol as
 *      fallback - the check offsetof() cannot do, a reordered table's slot having a different prototype.
 */
#define KSU_LSM_SLOTS_PER_HOOK	MAX_LSM_COUNT

/* arm64 kernel addresses (image, modules, vmalloc) all live in the top of the address space.
 * The bound is loose on purpose: it only has to reject NULL, a small integer, a user address. */
#define KSU_LSM_KPTR_MIN	0xff00000000000000UL

static unsigned long ksu_lsm_scalls_addr;

static bool ksu_lsm_kptr_plausible(const void *p)
{
    return (unsigned long)p >= KSU_LSM_KPTR_MIN;
}

/* Read one pointer-sized word without faulting.  @out is `void *`, not `void **`: callers
 * pass the address of a TYPED pointer and -Wincompatible-pointer-types is an error here. */
static int ksu_lsm_read_ptr(const void *addr, void *out)
{
    memset(out, 0, sizeof(void *));
    return (int)copy_from_kernel_nofault(out, addr, sizeof(void *));
}

/* Same implementation as @want?  Allows the ".clone"/".constprop.0" suffix a compiler adds. */
static bool ksu_lsm_name_is(const char *name, const char *want)
{
    size_t n = strlen(want);

    if (strncmp(name, want, n) != 0)
        return false;

    return name[n] == '\0' || name[n] == '.';
}

/* Is @fn the SELinux implementation of @member?  0 yes, negative no/unknown.  Primary source is the
 * kallsyms name for @fn (the function really registered); fallback the exact @expect; -ENOSYS = neither. */
static int ksu_lsm_fn_is_selinux_hook(void *fn, const char *member, void *expect)
{
    char buf[KSYM_SYMBOL_LEN];
    char want[64];
    char *mod = NULL;
    int len;

    snprintf(want, sizeof(want), "selinux_%s", member);

    len = ksu_symbol_name_of((unsigned long)fn, buf, &mod);
    if (len > 0)
        return (!mod && ksu_lsm_name_is(buf, want)) ? 0 : -EINVAL;

    if (expect)
        return (fn == expect) ? 0 : -EINVAL;

    return -ENOSYS;
}

/* Lock held; success sets ->scall/->entry/->original and the static call to the replacement. */
static int ksu_lsm_hook_insert_scall(struct ksu_lsm_hook *hook)
{
    struct lsm_static_call *slots;
    struct lsm_static_call *chosen = NULL;
    struct security_hook_list *chosen_hl = NULL;
    void *chosen_orig = NULL;
    void *expect = NULL;
    char want[64];
    int i, ret;

    if (!hook->head_name) {
        pr_err("lsm_hook: insert: hook has no head_name, cannot identify its static calls\n");
        return -EINVAL;
    }

    if (!ksu_lsm_scalls_addr) {
        ksu_lsm_scalls_addr = find_kernel_symbol_exact("static_calls_table");
        if (!ksu_lsm_scalls_addr) {
            pr_err("lsm_hook: insert: static_calls_table not resolved\n");
            return -ENOENT;
        }
        SUSFS_LOGI("lsm_hook: static_calls_table at %px (%d slots per hook)\n",
                (void *)ksu_lsm_scalls_addr, (int)KSU_LSM_SLOTS_PER_HOOK);
    }

    snprintf(want, sizeof(want), "selinux_%s", hook->head_name);
    expect = ksu_resolve_symbol_for_functable_hook(want);

    slots = (struct lsm_static_call *)(ksu_lsm_scalls_addr + hook->head_offset);

    for (i = 0; i < KSU_LSM_SLOTS_PER_HOOK; i++) {
        struct lsm_static_call *s = &slots[i];
        struct security_hook_list *hl;
        void *key, *tramp, *scalls, *lsmid, *namep, *hookfn, *cur;
        char namebuf[16];

        if (ksu_lsm_read_ptr(&s->key, &key) ||
            ksu_lsm_read_ptr(&s->trampoline, &tramp) ||
            ksu_lsm_read_ptr(&s->hl, &hl)) {
            pr_err("lsm_hook: insert: %s: slot %d of static_calls_table is not readable - refusing\n",
                    hook->head_name, i);
            return -EFAULT;
        }
        if (!hl)
            continue;	/* empty slot: no LSM implements this hook there */

        if (!key || !ksu_lsm_kptr_plausible(key) || !ksu_lsm_kptr_plausible(hl) ||
            (tramp && !ksu_lsm_kptr_plausible(tramp))) {
            pr_err("lsm_hook: insert: %s: slot %d has implausible key/trampoline/hl (%px/%px/%px) - struct lsm_static_call layout mismatch, refusing\n",
                    hook->head_name, i, key, tramp, hl);
            return -EINVAL;
        }

        if (ksu_lsm_read_ptr((const char *)hl + offsetof(struct security_hook_list, scalls), &scalls) ||
            scalls != (void *)slots) {
            pr_err("lsm_hook: insert: %s: slot %d entry %px reports scalls %px, expected %px - struct/table layout mismatch, refusing\n",
                    hook->head_name, i, hl, scalls, slots);
            return -EINVAL;
        }

        if (ksu_lsm_read_ptr((const char *)hl + offsetof(struct security_hook_list, lsmid), &lsmid) ||
            !ksu_lsm_kptr_plausible(lsmid) ||
            ksu_lsm_read_ptr((const char *)lsmid + offsetof(struct lsm_id, name), &namep) ||
            !ksu_lsm_kptr_plausible(namep) ||
            copy_from_kernel_nofault(namebuf, namep, 8)) {
            pr_err("lsm_hook: insert: %s: slot %d entry %px has no readable lsm_id name - refusing\n",
                    hook->head_name, i, hl);
            return -EINVAL;
        }
        namebuf[8] = '\0';
        if (strncmp(namebuf, "selinux", 8) != 0)
            continue;	/* capabilities, safesetid, landlock, bpf-lsm, ... */

        if (ksu_lsm_read_ptr((const char *)key + offsetof(struct static_call_key, func), &cur) ||
            ksu_lsm_read_ptr((const char *)hl + hook->hook_offset, &hookfn) ||
            !cur || !hookfn) {
            pr_err("lsm_hook: insert: %s: slot %d (selinux) has no readable current target - refusing\n",
                    hook->head_name, i);
            return -EINVAL;
        }
        if (cur != hookfn) {
            pr_err("lsm_hook: insert: %s: slot %d (selinux) calls %px while the entry's hook word holds %px - layout mismatch, refusing\n",
                    hook->head_name, i, cur, hookfn);
            return -EINVAL;
        }

        ret = ksu_lsm_fn_is_selinux_hook(cur, hook->head_name, expect);
        if (ret) {
            pr_err("lsm_hook: insert: %s: slot %d (selinux) holds %px, which is not %s (%d) - another owner or a shifted layout, refusing\n",
                    hook->head_name, i, cur, want, ret);
            return ret == -ENOSYS ? -ENOSYS : -EINVAL;
        }

        chosen = s;
        chosen_hl = hl;
        chosen_orig = cur;
        break;
    }

    if (!chosen) {
        pr_err("lsm_hook: insert: %s: no static-call slot owned by SELinux among the %d slots of this hook - refusing\n",
                hook->head_name, (int)KSU_LSM_SLOTS_PER_HOOK);
        return -ENOENT;
    }

    for (i = 0; i < ksu_lsm_hook_count; i++) {
        if (ksu_lsm_hook_entries[i].hook->scall == chosen) {
            pr_err("lsm_hook: insert: %s: that static-call slot is already taken over by %s\n",
                    hook->head_name, ksu_lsm_hook_entries[i].hook->head_name ?: "another hook");
            return -EALREADY;
        }
    }

    ret = ksu_lsm_hook_track(hook);
    if (ret) {
        pr_err("lsm_hook: too many hooks to track: %d\n", ret);
        return ret;
    }

    /* Publish in this order on purpose: the replacement reads hook->original on its
     * pass-through path, so it must become visible BEFORE the static call can reach it - a call in
     * between would see original == NULL and drop SELinux's decision.  The fence is needed on arm64
     * (static_call_update is a plain WRITE_ONCE of key->func, and the smp_wmb() inside
     * ksu_lsm_hook_update_scall() comes after that store); SUS_LSM_PASS_ORIG() has the matching
     * smp_rmb(), without which the reader can still load original before the key->func load. */
    hook->scall = chosen;
    hook->entry = chosen_hl;
    hook->original = chosen_orig;
    smp_wmb();
    ksu_lsm_hook_update_scall(chosen, hook->replacement);

    SUSFS_LOGI("lsm_hook: insert via static call slot (selinux, slot %d, %s static call) %s: %px -> %px\n",
            (int)(chosen - slots), chosen->trampoline ? "trampolined" : "key->func",
            hook->head_name, chosen_orig, hook->replacement);
    return 0;
}
#endif

int ksu_lsm_hook(struct ksu_lsm_hook *hook)
{
    int ret = 0;
    struct security_hook_list *entry;
    void *target;
    const char *target_name;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    static unsigned long scalls_addr = 0;
    struct lsm_static_call *scalls = NULL;
    static size_t scalls_count = 0;
    struct security_hook_list *selected_entry = NULL;
    struct lsm_static_call *selected_scall = NULL;
    void **selected_slot = NULL;
    void *selected_origin = NULL;
    size_t i;
#else
    unsigned long heads_addr;
    struct hlist_head *head;
    struct security_hook_list *selected_entry = NULL;
    void **selected_slot = NULL;
    void *selected_origin = NULL;
#endif

    if (!hook || !hook->replacement)
        return -EINVAL;

    mutex_lock(&ksu_lsm_hook_lock);

    if (hook->entry) {
        ret = -EALREADY;
        goto out_unlock;
    }

    if (hook->insert) {
        /* Insertion resolves no symbol on < 6.12 (no original, no slot to match), and both
         * branches validate everything before their first patched write. */
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
        ret = ksu_lsm_hook_insert_scall(hook);
        goto out_unlock;
#else
        heads_addr = find_kernel_symbol_exact("security_hook_heads");
        if (!heads_addr) {
            pr_err("lsm_hook: failed to resolve security_hook_heads\n");
            ret = -ENOENT;
            goto out_unlock;
        }

        ret = ksu_lsm_hook_head_at(heads_addr, hook, &head);
        if (ret)
            goto out_unlock;

        ret = ksu_lsm_hook_track(hook);
        if (ret) {
            pr_err("lsm_hook: too many hooks to track: %d\n", ret);
            goto out_unlock;
        }

        ret = ksu_lsm_hook_insert_head(hook, head);
        if (ret) {
            pr_err("lsm_hook: failed to insert %s at the head of its list: %d\n",
                    hook->head_name ?: "unknown", ret);
            ksu_lsm_hook_untrack(hook);
            goto out_unlock;
        }
        goto out_unlock;
#endif
    }

    /* ---- replace path: find the entry whose function slot holds the resolved symbol. ---- */
    target_name = hook->target_name;
    if (!target_name) {
        pr_err("lsm_hook: hook %s: target_name is required\n", hook->head_name ?: "unknown");
        ret = -EINVAL;
        goto out_unlock;
    }

    target = hook->original;
    if (!target)
        target = ksu_resolve_symbol_for_functable_hook(target_name);
    if (!target) {
        pr_err("lsm_hook: failed to resolve target for %s\n", hook->head_name ?: "unknown");
        ret = -ENOENT;
        goto out_unlock;
    }
    SUSFS_LOGI("target: 0x%lx %pSb\n", (unsigned long)target, target);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    if (!scalls_addr) {
        scalls_addr = find_kernel_symbol_exact("static_calls_table");
    }
    if (!scalls_addr) {
        pr_err("lsm_hook: failed to resolve static_calls_table\n");
        ret = -ENOSYS;
        goto out_unlock;
    }

    if (scalls_count == 0) {
        /* sym_size is sizeof() and not kallsyms_lookup_size_offset(): that symbol is UNEXPORTED
         * in every GKI tree this module targets, so importing it makes the module unloadable by
         * a plain `insmod` (unknown symbol) - it is the fifth name the "Verify sections" CI step
         * refuses in the .ko's undefined list - and the number is the same either way. */
        unsigned long sym_size = sizeof(struct lsm_static_calls_table);
        unsigned long addr = find_kernel_symbol_exact("lsm_active_cnt");

        /* The STRIDE is the compile-time MAX_LSM_COUNT the table is dimensioned with, NOT the
         * runtime number of active LSMs: lsm_active_cnt counts the enabled SECURITY_ options
         * (plus BPF_LSM etc.) and says nothing about how many slots each hook has.  Using it as
         * the stride picked the wrong struct lsm_static_call whenever the two differ, i.e.
         * patched a function pointer into another hook's slot (kCFI panic at the next call). */
        if (addr)
            SUSFS_LOGI("lsm_active_cnt = %d (only informational; the table stride is %d)\n",
                    (int)*(u32 *)addr, (int)KSU_LSM_SLOTS_PER_HOOK);

        if (sym_size % (KSU_LSM_SLOTS_PER_HOOK * sizeof(struct lsm_static_call)) != 0) {
            pr_warn("lsm_hook: static_calls_table is %lu bytes, not a whole number of %d-slot hooks\n",
                    sym_size, (int)KSU_LSM_SLOTS_PER_HOOK);
        }
        scalls_count = sym_size / sizeof(struct lsm_static_call);
        SUSFS_LOGI("scalls_count = %zu\n", scalls_count);
    }

    if (scalls_count == 0) {
        pr_err("no scalls_count found!\n");
        ret = -ENOSYS;
        goto out_unlock;
    }

    scalls = (struct lsm_static_call *)scalls_addr;
    for (i = 0; i < scalls_count; i++) {
        struct lsm_static_call *scall = &scalls[i];
        void **slot;
        void *current_origin;

        entry = READ_ONCE(scall->hl);
        if (!entry)
            continue;

        slot = (void **)((char *)entry + hook->hook_offset);
        current_origin = READ_ONCE(*slot);

        int j;
        for (j = 0; j < ksu_lsm_hook_count; j++) {
            if (ksu_lsm_hook_entries[j].hook->replacement == current_origin) {
                current_origin = ksu_lsm_hook_entries[j].hook->original;
                break;
            }
        }

        if (current_origin == hook->replacement) {
            ret = -EALREADY;
            goto out_unlock;
        }

        if (current_origin != target) {
            continue;
        }

        SUSFS_LOGI("found slot %ld orig %pSb\n", i, current_origin);

        if (!hook->offset) {
            selected_entry = entry;
            selected_scall = scall;
            selected_slot = slot;
            selected_origin = current_origin;
        } else {
            size_t hook_idx = (i / KSU_LSM_SLOTS_PER_HOOK + hook->offset) * KSU_LSM_SLOTS_PER_HOOK;
            if (hook_idx >= scalls_count) {
                pr_err("last lsm hook reached\n");
                ret = -EINVAL;
                goto out_unlock;
            }
            scall = &scalls[hook_idx];
            entry = READ_ONCE(scall->hl);
            if (entry) {
                slot = (void **)((char *)entry + hook->hook_offset);
                current_origin = READ_ONCE(*slot);
            } else {
                current_origin = NULL;
            }
            SUSFS_LOGI("found real slot %ld orig %pSb\n", i, current_origin);

            if (current_origin == hook->replacement) {
                ret = -EALREADY;
                goto out_unlock;
            }
            selected_entry = entry;
            selected_scall = scall;
            selected_slot = slot;
            selected_origin = current_origin;
        }
        break;
    }

    if (!selected_scall) {
        pr_err("lsm_hook: target %s not found in head %s\n", target_name, hook->head_name ?: "unknown");
        ret = -ENOENT;
        goto out_unlock;
    }

    ret = ksu_lsm_hook_track(hook);
    if (ret) {
        pr_err("lsm_hook: too many hooks to track: %d\n", ret);
        goto out_unlock;
    }

    if (ksu_lsm_hook_patch_slot(selected_slot, hook->replacement)) {
        pr_err("lsm_hook: failed to patch %s\n", hook->head_name ?: "unknown");
        ret = -EFAULT;
        goto out_untrack;
    }

    /* Publish BEFORE the switch, exactly like the insert path: the replacement reads
     * hook->original on its pass-through path, so a call arriving between the static-call
     * update and this store would see NULL and fall through to `return 0` - dropping
     * SELinux's decision (fail-open).  smp_wmb() pairs with the smp_rmb() in
     * SUS_LSM_PASS_ORIG(). */
    hook->entry = selected_entry;
    hook->scall = selected_scall;
    hook->original = selected_origin;
    smp_wmb();

    if (ksu_lsm_hook_update_scall(selected_scall, hook->replacement)) {
        /* Undo the publication as well: the replacement must not look armed, or a later
         * unhook would try to restore a static call that was never switched. */
        hook->entry = NULL;
        hook->scall = NULL;
        hook->original = NULL;
        if (ksu_lsm_hook_patch_slot(selected_slot, selected_origin)) {
            pr_err("lsm_hook: failed to roll back %s after static call update failure\n", hook->head_name ?: "unknown");
        }
        ret = -EFAULT;
        goto out_untrack;
    }

    if (!selected_origin)
        static_branch_enable(selected_scall->active);

    SUSFS_LOGI("lsm_hook: patched %s hook slot %px from %px to %px\n", hook->head_name ?: "unknown", selected_slot,
            selected_origin, hook->replacement);
#else
    heads_addr = find_kernel_symbol_exact("security_hook_heads");
    if (!heads_addr) {
        pr_err("lsm_hook: failed to resolve security_hook_heads\n");
        ret = -ENOENT;
        goto out_unlock;
    }
    unsigned long heads_size = sizeof(struct security_hook_heads);
    /* heads_size is sizeof(), not kallsyms_lookup_size_offset(), which is UNEXPORTED in every
     * GKI tree this module targets - see the same call site in the >= 6.12 branch. */

    head = (struct hlist_head *)heads_addr;
    struct hlist_head *head_end = (struct hlist_head *)(heads_addr + heads_size);
    SUSFS_LOGI("heads_addr 0x%lx head_offset 0x%lx heads_size %ld hook_offset 0x%lx\n", (unsigned long)heads_addr,
            hook->head_offset, heads_size, hook->hook_offset);

    for (; head < head_end; head++) {
        hlist_for_each_entry (entry, head, list) {
            void **slot = (void **)((char *)entry + hook->hook_offset);
            void *current_origin = READ_ONCE(*slot);
            int j;
            for (j = 0; j < ksu_lsm_hook_count; j++) {
                if (ksu_lsm_hook_entries[j].hook->replacement == current_origin) {
                    current_origin = ksu_lsm_hook_entries[j].hook->original;
                    break;
                }
            }
            if (current_origin == hook->replacement) {
                ret = -EALREADY;
                goto out_unlock;
            }
            if (current_origin == target) {
                SUSFS_LOGI("found %s (target %s) at head offset %ld (provided %ld)\n", hook->head_name, hook->target_name,
                        (unsigned long)head - heads_addr, hook->head_offset);
                selected_entry = entry;
                selected_slot = slot;
                selected_origin = current_origin;
                break;
            }
        }
        if (selected_entry) {
            if (hook->offset) {
                head += hook->offset;
                if (head < (struct hlist_head *)heads_addr || head >= head_end) {
                    pr_err("invalid offset\n");
                    ret = -EINVAL;
                    goto out_unlock;
                }
                hlist_for_each_entry (entry, head, list) {
                    void **slot = (void **)((char *)entry + hook->hook_offset);
                    void *current_origin = READ_ONCE(*slot);
                    if (current_origin == hook->replacement) {
                        ret = -EALREADY;
                        goto out_unlock;
                    }
                }
                if (head->first) {
                    selected_entry = hlist_entry(head->first, struct security_hook_list, list);
                    selected_slot = (void **)((char *)selected_entry + hook->hook_offset);
                    selected_origin = *selected_slot;
                } else {
                    selected_entry = &hook->list;
                    hook->list.head = head;
                    hook->list.list.next = NULL;
                    hook->list.list.pprev = &head->first;
                    hook->list.lsm = "ksu";
                    *(void **)((char *)selected_entry + hook->hook_offset) = hook->replacement;
                    selected_slot = (void **)&head->first;
                    selected_origin = NULL;
                }
            }
            break;
        }
    }

    if (!selected_entry) {
        pr_err("lsm_hook: target %s not found in head %s\n", target_name, hook->head_name ?: "unknown");
        ret = -ENOENT;
        goto out_unlock;
    }

    ret = ksu_lsm_hook_track(hook);
    if (ret) {
        pr_err("lsm_hook: too many hooks to track: %d\n", ret);
        goto out_unlock;
    }

    if (selected_origin) {
        SUSFS_LOGI("patch func addr\n");
        ret = ksu_lsm_hook_patch_slot(selected_slot, hook->replacement);
    } else {
        SUSFS_LOGI("patch head->first\n");
        ret = ksu_lsm_hook_patch_slot(selected_slot, &hook->list);
    }

    if (ret) {
        pr_err("lsm_hook: failed to patch %s\n", hook->head_name ?: "unknown");
        ret = -EFAULT;
        goto out_untrack;
    }

    hook->entry = selected_entry;
    hook->original = selected_origin;
    SUSFS_LOGI("lsm_hook: patched %s hook slot %px from %px to %px\n", hook->head_name ?: "unknown", selected_slot,
            selected_origin, hook->replacement);
#endif
    goto out_unlock;
out_untrack:
    ksu_lsm_hook_untrack(hook);

out_unlock:
    mutex_unlock(&ksu_lsm_hook_lock);
    return ret;
}

void ksu_lsm_unhook(struct ksu_lsm_hook *hook)
{
    void **slot;
    mutex_lock(&ksu_lsm_hook_lock);

#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    if (!hook->entry || !hook->scall) {
        mutex_unlock(&ksu_lsm_hook_lock);
        return;
    }
    if (hook->insert) {
        /* Symmetric with ksu_lsm_hook_insert_scall(): the takeover only replaced the
         * static call, and the entry's own hook word still holds the original. */
        if (ksu_lsm_hook_update_scall(hook->scall, hook->original)) {
            pr_err("lsm_hook: failed to restore the static call for %s\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        SUSFS_LOGI("lsm_hook: insert static call slot (selinux) for %s restored to %px\n",
                hook->head_name ?: "unknown", hook->original);
    } else {
        slot = (void **)((char *)hook->entry + hook->hook_offset);
        if (ksu_lsm_hook_patch_slot(slot, hook->original)) {
            pr_err("lsm_hook: failed to restore %s\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        if (ksu_lsm_hook_update_scall(hook->scall, hook->original)) {
            if (ksu_lsm_hook_patch_slot(slot, hook->replacement))
                pr_err("lsm_hook: failed to reapply %s after static call restore failure\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        SUSFS_LOGI("lsm_hook: restored %s hook slot %px to %px\n", hook->head_name ?: "unknown", slot, hook->original);
    }
#else
    if (!hook->entry) {
        mutex_unlock(&ksu_lsm_hook_lock);
        return;
    }

    if (hook->entry == &hook->list) {
        /* Our own security_hook_list node is in the list: an insert node, or (legacy) a
         * replace-mode hook that found its head empty; both unlink through list.pprev. */
        if (ksu_lsm_hook_remove_head(hook)) {
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
    } else {
        slot = (void **)((char *)hook->entry + hook->hook_offset);
        SUSFS_LOGI("unhook patch slot\n");
        if (ksu_lsm_hook_patch_slot(slot, hook->original)) {
            pr_err("lsm_hook: failed to restore %s\n", hook->head_name ?: "unknown");
            mutex_unlock(&ksu_lsm_hook_lock);
            return;
        }
        SUSFS_LOGI("lsm_hook: restored %s hook slot %px to %px\n", hook->head_name ?: "unknown", slot, hook->original);
    }
#endif

    ksu_lsm_hook_untrack(hook);
    hook->entry = NULL;
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 12, 0)
    hook->scall = NULL;
#endif
    mutex_unlock(&ksu_lsm_hook_lock);

    /* Drained after the lock is released: the wait is unbounded (a quiescent state for every
     * task, or the 50 ms fallback) and holding ksu_lsm_hook_lock across it serialises every
     * other hook operation, while the node/slot is already unlinked above and only a task
     * already inside the replacement can still be there. */
    ksu_lsm_hook_drain();
}

/* Wait until nothing can still be inside a replacement function.
 * synchronize_rcu() is not enough: the LSM call sites walk their hook list with a plain
 * hlist_for_each_entry (security/security.c), not through an RCU read-side section, so a task already
 * inside the replacement is invisible to that barrier and would still be there when the module text is
 * unmapped - a use-after-free on the next instruction.  synchronize_rcu_tasks() waits for every task to
 * pass a context switch, which does cover it; it is resolved at runtime and reached through a __nocfi
 * wrapper (kCFI checks the type hash at the call site), with a 50 ms delay if it cannot be resolved. */
static void (*ksu_lsm_sync_rcu_tasks_fn)(void);
static bool ksu_lsm_sync_looked_up;

static __nocfi void ksu_lsm_call_drain(void (*fn)(void))
{
    fn();
}

static void ksu_lsm_hook_drain(void)
{
    if (!ksu_lsm_sync_looked_up) {
        ksu_lsm_sync_rcu_tasks_fn =
            (void *)find_kernel_symbol_exact("synchronize_rcu_tasks");
        if (ksu_lsm_sync_rcu_tasks_fn) {
            /* Cache SUCCESS only - caching a failure keeps the 50 ms fallback forever. */
            ksu_lsm_sync_looked_up = true;
        } else {
            pr_warn("lsm_hook: synchronize_rcu_tasks not found, using a delay\n");
        }
    }

    synchronize_rcu();
    if (ksu_lsm_sync_rcu_tasks_fn)
        ksu_lsm_call_drain(ksu_lsm_sync_rcu_tasks_fn);
    else
        msleep(50);
}

int ksu_register_lsm_hook(struct ksu_lsm_hook *hook)
{
    return ksu_lsm_hook(hook);
}

void ksu_unregister_lsm_hook(struct ksu_lsm_hook *hook)
{
    ksu_lsm_unhook(hook);
}

/* No __init/__exit annotation on these two on purpose: the layer table (susfs_main.c) holds their
 * addresses and calls the exit from the rollback path of a FAILED load, i.e. from plain .text. */
void ksu_lsm_hook_init(void)
{
    SUSFS_LOGI("lsm_hook: init, tracked hooks=%d\n", READ_ONCE(ksu_lsm_hook_count));
}

void ksu_lsm_hook_exit(void)
{
    struct ksu_lsm_hook *hooks[ARRAY_SIZE(ksu_lsm_hook_entries)];
    int count;
    int i;

    mutex_lock(&ksu_lsm_hook_lock);
    count = ksu_lsm_hook_count;
    for (i = 0; i < count; i++)
        hooks[i] = ksu_lsm_hook_entries[i].hook;
    mutex_unlock(&ksu_lsm_hook_lock);

    for (i = count - 1; i >= 0; i--)
        ksu_lsm_unhook(hooks[i]);
}
