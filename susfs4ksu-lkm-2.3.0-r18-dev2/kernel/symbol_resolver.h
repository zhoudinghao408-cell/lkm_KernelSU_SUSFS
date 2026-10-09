/* SPDX-License-Identifier: GPL-2.0 */
#ifndef __SUSFS_SYMBOL_RESOLVER_H
#define __SUSFS_SYMBOL_RESOLVER_H

void *ksu_resolve_symbol_for_functable_hook(const char *symbol_name);
unsigned long find_kernel_symbol_exact(const char *symbol_name);
/* EVERY vmlinux symbol with this exact name (not just the first): a kprobe registered with
 * .symbol_name attaches to whichever match kallsyms lists first, and not every name is unique
 * (measured: `seq_show` exists four times from 6.1 on, once on 5.10/5.15).  Writes at most
 * @max addresses and returns how many were written (0 = unknown/not found). */
int ksu_find_symbol_all(const char *name, unsigned long *addrs, int max);
/* Name of the symbol containing @addr (vmlinux only unless @module_out says otherwise): -ENOSYS when
 * kallsyms_lookup() was not bootstrapped, -ENOENT when the address cannot be named, else the length written;
 * @buf must be KSYM_SYMBOL_LEN bytes.  lsm_hook.c's static-call takeover uses it to check that the slot it is
 * about to steal really belongs to the hook it is installing for. */
int ksu_symbol_name_of(unsigned long addr, char *buf, char **module_out);
void ksu_init_symbol_resolver(void);

#endif
