/*
 * Copyright (C) 2025 pdnguyen of HCMC University of Technology VNU-HCM
 */

/* Sierra release
 * Source Code License Grant: The authors hereby grant to Licensee
 * personal permission to use and modify the Licensed Source Code
 * for the sole purpose of studying while attending the course CO2018.
 */

// #ifdef MM_PAGING
/*
 * System Library
 * Memory Module Library libmem.c 
 */

#include "string.h"
#include "mm.h"
#include "syscall.h"
#include "libmem.h"
#include <stdlib.h>
#include <stdio.h>
#include <pthread.h>

static pthread_mutex_t mmvm_lock = PTHREAD_MUTEX_INITIALIZER;

/*enlist_vm_freerg_list - add new rg to freerg_list
 *@mm: memory region
 *@rg_elmt: new region
 *
 */
int enlist_vm_freerg_list(struct mm_struct *mm, struct vm_rg_struct *rg_elmt)
{
  struct vm_rg_struct *rg_node = mm->mmap->vm_freerg_list;

  if (rg_elmt->rg_start >= rg_elmt->rg_end)
    return -1;

  if (rg_node != NULL)
    rg_elmt->rg_next = rg_node;

  /* Enlist the new region */
  mm->mmap->vm_freerg_list = rg_elmt;

  return 0;
}

/*get_symrg_byid - get mem region by region ID
 *@mm: memory region
 *@rgid: region ID act as symbol index of variable
 *
 */
struct vm_rg_struct *get_symrg_byid(struct mm_struct *mm, int rgid)
{
  if (rgid < 0 || rgid > PAGING_MAX_SYMTBL_SZ)
    return NULL;

  return &mm->symrgtbl[rgid];
}

/*__alloc - allocate a region memory
 *@caller: caller
 *@vmaid: ID vm area to alloc memory region
 *@rgid: memory region ID (used to identify variable in symbole table)
 *@size: allocated size
 *@alloc_addr: address of allocated memory region
 *
 */

int __alloc(struct pcb_t *caller, int vmaid, int rgid, int size, int *alloc_addr)
{
  /*Allocate at the toproof */
  struct vm_rg_struct rgnode;

  /* TODO: commit the vmaid */
  // rgnode.vmaid = vmaid;

  struct vm_area_struct *cur_vma = get_vma_by_num(caller->mm, vmaid);
  if (cur_vma == NULL) {
      pthread_mutex_unlock(&mmvm_lock);
      return -1;
  }

  if (get_free_vmrg_area(caller, vmaid, size, &rgnode) == 0)
  {
    caller->mm->symrgtbl[rgid].rg_start = rgnode.rg_start;
    caller->mm->symrgtbl[rgid].rg_end = rgnode.rg_end;
 
    *alloc_addr = rgnode.rg_start;

    pthread_mutex_unlock(&mmvm_lock);
    return 0;
  }
  /* TODO get_free_vmrg_area FAILED handle the region management (Fig.6)*/
  /* TODO retrive current vma if needed, current comment out due to compiler redundant warning*/
  /* Attempt to increase limit to get space */
  /* TODO retrive old_sbrk if needed, current comment out due to compiler redundant warning*/
  int old_sbrk = cur_vma->sbrk;
  /* TODO INCREASE THE LIMIT as invoking systemcall 
   * sys_memap with SYSMEM_INC_OP 
   */
  struct sc_regs regs;
  regs.a1 = cur_vma->vm_id;  // Lấy vm_id từ VMA (vì vm_rg_struct không chứa trường này)
  regs.a2 = old_sbrk;
  regs.a3 = PAGING_PAGE_ALIGNSZ(size);
  
  /* SYSCALL 17 sys_memmap */
  int ret = syscall(17, SYSMEM_INC_OP, &regs);
  if (ret < 0) {
      pthread_mutex_unlock(&mmvm_lock);
      return -1;
  }
  /* TODO: commit the limit increment */
  cur_vma->sbrk += PAGING_PAGE_ALIGNSZ(size);
  /* TODO: commit the allocation address */
  *alloc_addr = old_sbrk;
  caller->mm->symrgtbl[rgid].rg_start = old_sbrk;
  caller->mm->symrgtbl[rgid].rg_end = old_sbrk + size;

  pthread_mutex_unlock(&mmvm_lock);
  return 0;
}


/*__free - remove a region memory
 *@caller: caller
 *@vmaid: ID vm area to alloc memory region
 *@rgid: memory region ID (used to identify variable in symbole table)
 *@size: allocated size
 *

/*liballoc - PAGING-based allocate a region memory
 *@proc:  Process executing the instruction
 *@size: allocated size
 *@reg_index: memory region ID (used to identify variable in symbole table)
 */
int liballoc(struct pcb_t *proc, uint32_t size, uint32_t reg_index)
{
  /* TODO Implement allocation on vm area 0 */
  int addr;

  /* By default using vmaid = 0 */
  return __alloc(proc, 0, reg_index, size, &addr);
}

/*libfree - PAGING-based free a region memory
 *@proc: Process executing the instruction
 *@size: allocated size
 *@reg_index: memory region ID (used to identify variable in symbole table)
 */
int __free(struct pcb_t *caller, int vmaid, int rgid)
{
  pthread_mutex_lock(&mmvm_lock);

  struct vm_rg_struct *rgnode = get_symrg_byid(caller->mm, rgid);
  if (rgnode == NULL || rgnode->rg_start >= rgnode->rg_end) {
    pthread_mutex_unlock(&mmvm_lock);
    return -1; 
  }

  struct vm_rg_struct *free_rg = (struct vm_rg_struct*)malloc(sizeof(struct vm_rg_struct));
  if (free_rg == NULL) {
    pthread_mutex_unlock(&mmvm_lock);
    return -1;
  }

  free_rg->rg_start = rgnode->rg_start;
  free_rg->rg_end = rgnode->rg_end;
  free_rg->rg_next = NULL;

  struct vm_area_struct *cur_vma = get_vma_by_num(caller->mm, vmaid);
  if (cur_vma == NULL) {
    free(free_rg);
    pthread_mutex_unlock(&mmvm_lock);
    return -1; 
  }

  int ret = enlist_vm_freerg_list(caller->mm, free_rg);
  
  rgnode->rg_start = 0;
  rgnode->rg_end = 0;

  pthread_mutex_unlock(&mmvm_lock);
  return ret;
}



int libfree(struct pcb_t *proc, uint32_t reg_index)
{
  /* Implementation of free region */
  if (reg_index < 0 || reg_index >= PAGING_MAX_SYMTBL_SZ) {
    return -1; // Invalid region index
  }

  /* By default using vmaid = 0 */
  return __free(proc, 0, reg_index);
}

/*pg_getpage - get the page in ram
 *@mm: memory region
 *@pagenum: PGN
 *@framenum: return FPN
 *@caller: caller
 *
 */
int pg_getpage(struct mm_struct *mm, int pgn, int *fpn, struct pcb_t *caller)
{
  uint32_t pte = mm->pgd[pgn];

  if (!PAGING_PAGE_PRESENT(pte))
  { /* Page is not online, make it actively living */
    int vicpgn, swpfpn; 
    int vicfpn;
    uint32_t vicpte;

    int tgtfpn = PAGING_PTE_SWP(pte); // Target frame in swap space

    /* Find victim page to replace */
    find_victim_page(caller->mm, &vicpgn);
    
    /* Get victim page's frame number */
    vicpte = mm->pgd[vicpgn];
    vicfpn = PAGING_FPN(vicpte);

    /* Get free frame in swap space */
    MEMPHY_get_freefp(caller->active_mswp, &swpfpn);

    /* Copy victim frame to swap space */
    struct sc_regs regs;
    regs.a1 = vicfpn;     // Source frame (in RAM)
    regs.a2 = swpfpn;     // Destination frame (in swap)
    regs.a3 = 0;          // Additional parameters if needed

    /* Execute swap operation */
    syscall(17, SYSMEM_SWP_OP, &regs);

    /* Update victim's page table entry - mark as swapped out */
    pte_set_swap(&mm->pgd[vicpgn], swpfpn, 1);

    /* Copy target frame from swap to RAM */
    regs.a1 = tgtfpn;     // Source frame (in swap)
    regs.a2 = vicfpn;     // Destination frame (in RAM)
    regs.a3 = 0;          // Additional parameters if needed

    /* Execute swap operation */
    syscall(17, SYSMEM_SWP_OP, &regs);

    /* Update target page's page table entry - mark as present in RAM */
    pte_set_fpn(&mm->pgd[pgn], vicfpn);

    /* Add page to FIFO queue for future page replacement */
    struct pgn_t *pg_node = (struct pgn_t*)malloc(sizeof(struct pgn_t));
    if (pg_node != NULL) {
      pg_node->pgn = pgn;
      pg_node->pg_next = NULL;
      enlist_pgn_node(caller->mm, pg_node); // Correct call with proper node creation
    }
  }

  /* Return the frame page number */
  *fpn = PAGING_FPN(mm->pgd[pgn]);

  return 0;
}

/*pg_getval - read value at given offset
 *@mm: memory region
 *@addr: virtual address to acess
 *@value: value
 *
 */
int pg_getval(struct mm_struct *mm, int addr, BYTE *data, struct pcb_t *caller)
{
  int pgn = PAGING_PGN(addr);
  int off = PAGING_OFFST(addr);
  int fpn;

  /* Get the page to MEMRAM, swap from MEMSWAP if needed */
  if (pg_getpage(mm, pgn, &fpn, caller) != 0)
    return -1; /* invalid page access */

  /* Calculate physical address from frame number and offset */
  int phyaddr = (fpn << 8) | off;  // 8 bits for offset (256 bytes per page)

  /* Set up system call to read from physical memory */
  struct sc_regs regs;
  regs.a1 = phyaddr;        // Physical address to read from
  regs.a2 = (uint32_t)data; // Where to store the result
  regs.a3 = 1;              // Read 1 byte

  /* SYSCALL 17 sys_memmap with SYSMEM_IO_READ operation */
  return syscall(17, SYSMEM_IO_READ, &regs);
}

/*pg_setval - write value to given offset
 *@mm: memory region
 *@addr: virtual address to acess
 *@value: value
 *
 */
int pg_setval(struct mm_struct *mm, int addr, BYTE value, struct pcb_t *caller)
{
  int pgn = PAGING_PGN(addr);
  int off = PAGING_OFFST(addr);
  int fpn;

  if (pg_getpage(mm, pgn, &fpn, caller) != 0)
    return -1; /* invalid page access */

  int phyaddr = (fpn << 8) | off;  // 8 bits for offset (256 bytes per page)

  struct sc_regs regs;
  regs.a1 = phyaddr;        // Physical address to write to
  regs.a2 = (uint32_t)value; // Value to write
  regs.a3 = 1;              // Write 1 byte

  /* SYSCALL 17 sys_memmap with SYSMEM_IO_WRITE operation */
  return syscall(17, SYSMEM_IO_WRITE, &regs);
}

/*__read - read value in region memory
 *@caller: caller
 *@vmaid: ID vm area to alloc memory region
 *@offset: offset to acess in memory region
 *@rgid: memory region ID (used to identify variable in symbole table)
 *@size: allocated size
 *
 */
int __read(struct pcb_t *caller, int vmaid, int rgid, int offset, BYTE *data)
{
  struct vm_rg_struct *currg = get_symrg_byid(caller->mm, rgid);
  struct vm_area_struct *cur_vma = get_vma_by_num(caller->mm, vmaid);

  if (currg == NULL || cur_vma == NULL) /* Invalid memory identify */
    return -1;

  pg_getval(caller->mm, currg->rg_start + offset, data, caller);

  return 0;
}

/*libread - PAGING-based read a region memory */
int libread(
    struct pcb_t *proc, // Process executing the instruction
    uint32_t source,    // Index of source register
    uint32_t offset,    // Source address = [source] + [offset]
    uint32_t* destination)
{
  BYTE data;
  int val = __read(proc, 0, source, offset, &data);

  /* TODO update result of reading action*/
  //destination 
#ifdef IODUMP
  printf("read region=%d offset=%d value=%d\n", source, offset, data);
#ifdef PAGETBL_DUMP
  print_pgtbl(proc, 0, -1); //print max TBL
#endif
  MEMPHY_dump(proc->mram);
#endif

  return val;
}

/*__write - write a region memory
 *@caller: caller
 *@vmaid: ID vm area to alloc memory region
 *@offset: offset to acess in memory region
 *@rgid: memory region ID (used to identify variable in symbole table)
 *@size: allocated size
 *
 */
int __write(struct pcb_t *caller, int vmaid, int rgid, int offset, BYTE value)
{
  struct vm_rg_struct *currg = get_symrg_byid(caller->mm, rgid);
  struct vm_area_struct *cur_vma = get_vma_by_num(caller->mm, vmaid);

  if (currg == NULL || cur_vma == NULL) /* Invalid memory identify */
    return -1;

  pg_setval(caller->mm, currg->rg_start + offset, value, caller);

  return 0;
}

/*libwrite - PAGING-based write a region memory */
int libwrite(
    struct pcb_t *proc,   // Process executing the instruction
    BYTE data,            // Data to be wrttien into memory
    uint32_t destination, // Index of destination register
    uint32_t offset)
{
#ifdef IODUMP
  printf("write region=%d offset=%d value=%d\n", destination, offset, data);
#ifdef PAGETBL_DUMP
  print_pgtbl(proc, 0, -1); //print max TBL
#endif
  MEMPHY_dump(proc->mram);
#endif

  return __write(proc, 0, destination, offset, data);
}

/*free_pcb_memphy - collect all memphy of pcb
 *@caller: caller
 *@vmaid: ID vm area to alloc memory region
 *@incpgnum: number of page
 */
int free_pcb_memph(struct pcb_t *caller)
{
  int pagenum, fpn;
  uint32_t pte;


  for(pagenum = 0; pagenum < PAGING_MAX_PGN; pagenum++)
  {
    pte= caller->mm->pgd[pagenum];

    if (!PAGING_PAGE_PRESENT(pte))
    {
      fpn = PAGING_PTE_FPN(pte);
      MEMPHY_put_freefp(caller->mram, fpn);
    } else {
      fpn = PAGING_PTE_SWP(pte);
      MEMPHY_put_freefp(caller->active_mswp, fpn);    
    }
  }

  return 0;
}


/*find_victim_page - find victim page
 *@caller: caller
 *@pgn: return page number
 *
 */
int find_victim_page(struct mm_struct *mm, int *retpgn)
{
  struct pgn_t *pg = mm->fifo_pgn;

  if (pg == NULL) {
    return -1; 
  }
  
  *retpgn = pg->pgn;
  
  mm->fifo_pgn = pg->pg_next;
  
  free(pg);
  
  return 0;  // Success
}

/*get_free_vmrg_area - get a free vm region
 *@caller: caller
 *@vmaid: ID vm area to alloc memory region
 *@size: allocated size
 *
 */
int get_free_vmrg_area(struct pcb_t *caller, int vmaid, int size, struct vm_rg_struct *newrg)
{
  struct vm_area_struct *cur_vma = get_vma_by_num(caller->mm, vmaid);

  struct vm_rg_struct *rgit = cur_vma->vm_freerg_list;

  if (rgit == NULL)
    return -1;

  /* Probe unintialized newrg */
  newrg->rg_start = newrg->rg_end = -1;

  /* TODO Traverse on list of free vm region to find a fit space */
  struct vm_rg_struct *prev = NULL;
  
  while (rgit != NULL) {
    int region_size = rgit->rg_end - rgit->rg_start;
    
    if (region_size >= size) {
      newrg->rg_start = rgit->rg_start;
      newrg->rg_end = rgit->rg_start + size;
      newrg->rg_next = NULL; 
      
      if (region_size == size) {
        if (prev == NULL) {
          cur_vma->vm_freerg_list = rgit->rg_next;
        } else {
          prev->rg_next = rgit->rg_next;
        }
        free(rgit);
      } else {
        rgit->rg_start += size;
      }
      
      return 0; // Success
    }
    
    prev = rgit;
    rgit = rgit->rg_next;
  }

  return -1; // No suitable region found
}

//#endif
