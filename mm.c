/*- -*- mode: c; c-basic-offset: 8; -*-
 *
 * Simple, 32-bit and 64-bit clean allocator based on an implicit free list,
 * first fit placement, and boundary tag coalescing, as described in the
 * CS:APP2e text.  Blocks are aligned to double-word boundaries.  This
 * yields 8-byte aligned blocks on a 32-bit processor, and 16-byte aligned
 * blocks on a 64-bit processor.  However, 16-byte alignment is stricter
 * than necessary; the assignment only requires 8-byte alignment.  The
 * minimum block size is four words.
 *
 * This allocator uses the size of a pointer, e.g., sizeof(void *), to
 * define the size of a word.  This allocator also uses the standard
 * type uintptr_t to define unsigned integers that are the same size
 * as a pointer, i.e., sizeof(uintptr_t) == sizeof(void *).
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include "memlib.h"
#include "mm.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
	/* Team name */
	"Abc",
	/* First member's full name */
	"David Nichol",
	/* First member's email address */
	"dan1@rice.edu",
	/* Second member's full name (leave blank if none) */
	"John Cheng",
	/* Second member's email address (leave blank if none) */
	"jdc5@rice.edu"
};

/* Basic constants and macros: */
#define WSIZE      sizeof(void *) /* Word and header/footer size (bytes) */
#define DSIZE      (2 * WSIZE)    /* Doubleword size (bytes) */
#define CHUNKSIZE  (1 << 12)      /* Extend heap by this amount (bytes) */

#define MAX(x, y)  ((x) > (y) ? (x) : (y))  

/* Pack a size and allocated bit into a word. */
#define PACK(size, alloc)  ((size) | (alloc))

/* Read and write a word at address p. */
#define GET(p)       (*(uintptr_t *)(p))
#define PUT(p, val)  (*(uintptr_t *)(p) = (val))

/* Read the size and allocated fields from address p. */
#define GET_SIZE(p)   (GET(p) & ~(WSIZE - 1))
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer. */
#define HDRP(bp)  ((char *)(bp) - WSIZE)
#define FTRP(bp)  ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks. */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

#define NEXT_PTR(bp) FTRP(bp) - WSIZE
#define PREV_PTR(bp) FTRP(bp) - 2*WSIZE

/* Global variables: */
static char *heap_listp; /* Pointer to first block */  
static void *last_bp; /* Pointer to the last used block */
static uintptr_t beginning_listp;

/* Function prototypes for internal helper routines: */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);

static void place(void *bp, size_t asize);
void *find_fit(size_t asize);
void *first_fit(size_t asize);
void *explicit_first_fit(size_t asize);
void *next_fit(size_t asize);
void *best_fit(size_t asize);
void *explicit_best_fit(size_t asize);

/* Function prototypes for heap consistency checker routine	s: */
static void checkblock(void *bp);
static void checkheap(bool verbose);
static void printblock(void *bp); 

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Initialize the memory manager.  Returns 0 if the memory manager was
 *   successfully initialized and -1 otherwise.
 */
int
mm_init(void) 
{

	/* Create the initial empty heap. */
	if ((heap_listp = mem_sbrk(5 * WSIZE)) == (void *)-1)
		return (-1);
	PUT(heap_listp, 0);                            /* Alignment padding */
	PUT(heap_listp + (1 * WSIZE), PACK(WSIZE, 1)); /* Prologue header */
	PUT(heap_listp + (2 * WSIZE), PACK(WSIZE, 1)); /* Prologue footer */ 
	PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
	heap_listp += (2 * WSIZE);

	last_bp = heap_listp;
	beginning_listp = 0;
	/* Extend the empty heap with a free block of CHUNKSIZE bytes. */
	if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
		return (-1);
	return (0);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Allocate a block with at least "size" bytes of payload, unless "size" is
 *   zero.  Returns the address of this block if the allocation was successful
 *   and NULL otherwise.
 */
void *
mm_malloc(size_t size) 
{
	size_t asize;      /* Adjusted block size */
	size_t extendsize; /* Amount to extend heap if no fit */
	void *bp;

	/* Ignore spurious requests. */
	if (size == 0)
		return (NULL);

	/* Adjust block size to include overhead and alignment reqs. */
	if (size <= WSIZE)
		asize = 5 * WSIZE;
	else {
		asize = size + 2 * DSIZE;
		asize = WSIZE * ((asize + (WSIZE - 1)) / WSIZE);
	}

	/* Search the free list for a fit. */
	if ((bp = find_fit(asize)) != NULL) {
		place(bp, asize);
		return bp;
		
	}

	/* No fit found.  Get more memory and place the block. */
	extendsize = MAX(asize, CHUNKSIZE);
	if ((bp = extend_heap(extendsize / WSIZE)) == NULL)  
		return (NULL);
	place(bp, asize);
	return bp;
} 

/* 
 * Requires:
 *   "bp" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Free a block.
 */
void
mm_free(void *bp)
{
	size_t size;

	/* Ignore spurious requests. */
	if (bp == NULL)
		return;

	/* Free and coalesce the block. */
	size = GET_SIZE(HDRP(bp));
	PUT(HDRP(bp), PACK(size, 0));
	PUT(FTRP(bp), PACK(size, 0));
	
	
	bp = coalesce(bp);

	PUT(PREV_PTR(bp), 0);
	PUT(NEXT_PTR(bp), beginning_listp);
	
	if (beginning_listp) {
		PUT(PREV_PTR(beginning_listp), (uintptr_t) bp);
	}
	if ((uintptr_t)bp == beginning_listp) {
		printf("We've got a problem\n");
	}
	beginning_listp = (uintptr_t)bp;
		
}

/*
 * Requires:
 *   "ptr" is either the address of an allocated block or NULL.
 *
 * Effects:
 *   Reallocates the block "ptr" to a block with at least "size" bytes of
 *   payload, unless "size" is zero.  If "size" is zero, frees the block
 *   "ptr" and returns NULL.  If the block "ptr" is already a block with at
 *   least "size" bytes of payload, then "ptr" may optionally be returned.
 *   Otherwise, a new block is allocated and the contents of the old block
 *   "ptr" are copied to that new block.  Returns the address of this new
 *   block if the allocation was successful and NULL otherwise.
 */
void *
mm_realloc(void *ptr, size_t size)
{
	size_t oldsize;
	void *newptr;

	/* If size == 0 then this is just free, and we return NULL. */
	if (size == 0) {
		mm_free(ptr);
		return (NULL);
	}

	/* If oldptr is NULL, then this is just malloc. */
	if (ptr == NULL)
		return (mm_malloc(size));

	newptr = mm_malloc(size);

	/* If realloc() fails the original block is left untouched  */
	if (newptr == NULL)
		return (NULL);

	/* Copy the old data. */
	oldsize = GET_SIZE(HDRP(ptr));
	if (size < oldsize)
		oldsize = size;
	memcpy(newptr, ptr, oldsize);

	/* Free the old block. */
	mm_free(ptr);

	return (newptr);
}

/*
 * The following routines are internal helper routines.
 */

/*
 * Requires:
 *   "bp" is the address of a newly freed block.
 * 
 *
 * Effects:
 *   Perform boundary tag coalescing.  Returns the address of the coalesced
 *   block.
 */
static void *
coalesce(void *bp) 
{

	bool prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
	bool next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

	if ((PREV_BLKP(bp)) == bp) {
		prev_alloc = 1;
//		printf("%p\n", (void*)prev_alloc);
//		printf("asdfasdffsda;ljk %p adfsl;jk %p\n", bp, PREV_BLKP(bp));
	}
	size_t size = GET_SIZE(HDRP(bp));
	
	int D = -1;
	if (8==D) {
		printf("BSWB");
	}
	
	if (prev_alloc && next_alloc) {                 /* Case 1 */
		//printf("1\n");
		return (bp);
	} else if (prev_alloc && !next_alloc) {         /* Case 2 */
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
		if (last_bp == NEXT_BLKP(bp)) {
			last_bp = bp;
		}
		
		uintptr_t next_block_succ = GET(NEXT_PTR(NEXT_BLKP(bp)));
		uintptr_t next_block_pred = GET(PREV_PTR(NEXT_BLKP(bp)));
		
	//	printf("NEXT: ");
	//	printblock(NEXT_BLKP(bp));
		if (next_block_succ && next_block_pred) {
	//		printf("a\n");
			PUT(PREV_PTR(next_block_succ), next_block_pred);
			PUT(NEXT_PTR(next_block_pred), next_block_succ);
		}
		else if (next_block_succ && !next_block_pred) { // Means next block is beggining of list
	//		printf("b\n");
			PUT(PREV_PTR(next_block_succ), 0);
			beginning_listp = next_block_succ;
		}
		else if (!next_block_succ && next_block_pred) {
		//	printf("c\n");
			PUT(NEXT_PTR(next_block_pred), 0);	
		}
		else {
			//printf("d\n");
			beginning_listp = 0;
		}
		
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		//printf("2\n");
	} else if (!prev_alloc && next_alloc) {         /* Case 3 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));

		if (bp == last_bp) {
			last_bp = PREV_BLKP(bp);
		}
		//TODO: Don't do this.
		uintptr_t prev_block_succ = GET(NEXT_PTR(PREV_BLKP(bp)));
		uintptr_t prev_block_pred = GET(PREV_PTR(PREV_BLKP(bp)));
				
		if (prev_block_succ && prev_block_pred) {
		//	printf("cur bp %p prev BP %p SIZE %p \n", bp, (void *)PREV_BLKP(bp), (void *)GET_SIZE(HDRP(bp)));
			
		//	printf("PREV %p SUCC %p \n", (void *)prev_block_pred, (void *)prev_block_succ);
			PUT(PREV_PTR(prev_block_succ), prev_block_pred);
			PUT(NEXT_PTR(prev_block_pred), prev_block_succ);
		}
		else if (prev_block_succ && !prev_block_pred) { // Means next block is beggining of list
			PUT(PREV_PTR(prev_block_succ), 0);
			beginning_listp = prev_block_succ;
		}
		else if (!prev_block_succ && prev_block_pred) {
			PUT(NEXT_PTR(prev_block_pred), 0);	
		}
		else {
			beginning_listp = 0;
		}
		
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		//printf("3\n");
	} else {                                        /* Case 4 */
		size += GET_SIZE(HDRP(PREV_BLKP(bp))) + 
		    GET_SIZE(FTRP(NEXT_BLKP(bp)));

		if (bp == last_bp) {
			last_bp = PREV_BLKP(bp);
		}
		else if (last_bp == NEXT_BLKP(bp)) {
			last_bp = PREV_BLKP(bp);
		}
		
		uintptr_t next_block_succ = GET(NEXT_PTR(NEXT_BLKP(bp)));
		uintptr_t next_block_pred = GET(PREV_PTR(NEXT_BLKP(bp)));
					
		if (next_block_succ && next_block_pred) {
			PUT(PREV_PTR(next_block_succ), next_block_pred);
			PUT(NEXT_PTR(next_block_pred), next_block_succ);
		}
		else if (next_block_succ && !next_block_pred) { // Means next block is beggining of list
			PUT(PREV_PTR(next_block_succ), 0);
			beginning_listp = next_block_succ;
		}
		else if (!next_block_succ && next_block_pred) {
			PUT(NEXT_PTR(next_block_pred), 0);	
		}
		else {
			beginning_listp = 0;
		}
		
		//TODO: Don't do this.
		uintptr_t prev_block_succ = GET(NEXT_PTR(PREV_BLKP(bp)));
		uintptr_t prev_block_pred = GET(PREV_PTR(PREV_BLKP(bp)));
	

		if (prev_block_succ && prev_block_pred) {
			PUT(PREV_PTR(prev_block_succ), prev_block_pred);
			PUT(NEXT_PTR(prev_block_pred), prev_block_succ);
		}
		else if (prev_block_succ && !prev_block_pred) { // Means next block is beggining of list
			PUT(PREV_PTR(prev_block_succ), 0);
			beginning_listp = prev_block_succ;
		}
		else if (!prev_block_succ && prev_block_pred) {
			PUT(NEXT_PTR(prev_block_pred), 0);	
		}
		else {
			beginning_listp = 0;
		}
				
		bp = PREV_BLKP(bp);
		PUT(HDRP(bp), PACK(size, 0));
		PUT(FTRP(bp), PACK(size, 0));
		//printf("4\n");
		
	}
	return (bp);
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Extend the heap with a free block and return that block's address.
 */
static void *
extend_heap(size_t words) 
{
	void *bp;
	size_t size;

	/* Allocate an even number of words to maintain alignment. */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;
	if ((bp = mem_sbrk(size)) == (void *)-1)  
		return (NULL);

	/* Initialize free block header/footer and the epilogue header. */
	PUT(HDRP(bp), PACK(size, 0));         /* Free block header */
	PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */
	
	//printf("BP %p\n", bp);
	
	if (bp == (void*)beginning_listp) {
		PUT(NEXT_PTR(bp), 0);
		PUT(PREV_PTR(bp), 0);		
		printf("ok\n");
	}
	else {

		PUT(NEXT_PTR(bp), beginning_listp);
		if (beginning_listp) {
			PUT(PREV_PTR(beginning_listp), (uintptr_t)bp);
		}
		PUT(PREV_PTR(bp), 0);
			
		beginning_listp = (uintptr_t)bp;
	}

	/* Coalesce if the previous block was free. */
//	return (coalesce(bp));
	

	return bp;	
}

/*
 * Requires:
 *   None.
 *
 * Effects:
 *   Find a fit for a block with "asize" bytes.  Returns that block's address
 *   or NULL if no suitable block was found. 
 */
void *
find_fit(size_t asize)
{
	if (0) {
		first_fit(asize);
		next_fit(asize);
		best_fit(asize);
		explicit_first_fit(asize);
	}
	//return first_fit(asize);
	//return next_fit(asize);
	//return best_fit(asize);
	return explicit_first_fit(asize);
	//return explicit_best_fit(asize);
		
}


void* 
first_fit(size_t asize)
{
	void *bp;
	/* Search for the first fit. */
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = (NEXT_BLKP(bp))) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp)))
			return (bp);
	}
	/* No fit was found. */
	return (NULL);
}

void* 
explicit_first_fit(size_t asize)
{
	void *bp;
	void *prev = NULL;
	/* Search for the first fit. */
	for (bp = (void*)beginning_listp; bp; bp = (void*)GET(NEXT_PTR(bp))) {
		if (bp==(void*)GET(NEXT_PTR(bp))) {
			printf("error: infinate loop\n");
		}
		prev = bp;

		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {
			return (bp);
		}
	}

	/* No fit was found. */
	return (NULL);
}



void *
next_fit(size_t asize)
{
	void *bp;
	void *bp2;

	/* Search for the first fit. */
	for (bp = NEXT_BLKP(last_bp); GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp)) && asize <= GET_SIZE(HDRP(bp))) {

			last_bp = bp;
			return (bp);
		}
	}
	for (bp2 = heap_listp; bp2 < last_bp; bp2 = NEXT_BLKP(bp2)) {

		if (!GET_ALLOC(HDRP(bp2)) && asize <= GET_SIZE(HDRP(bp2))) {
			last_bp = bp2; 
			return (bp2);
		}
	}
	/* No fit was found. */
	last_bp = heap_listp;

	return (NULL);
}

void* best_fit(size_t asize)
{
	void *bp;
	void *minimum_pointer = NULL;
	
	/* Search for the best fit. */
	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (!GET_ALLOC(HDRP(bp))) {
			if (asize == GET_SIZE(HDRP(bp))) {
				return (bp);
			}
			else if (GET_SIZE(HDRP(bp)) > asize && (!minimum_pointer || (GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(minimum_pointer))))) {
				minimum_pointer = bp;
			}
		}
	}

	return (minimum_pointer);
}


void* 
explicit_best_fit(size_t asize)
{
	void *bp;
	void *minimum_pointer = NULL;

	/* Search for the best fit. */
	for (bp = (void*)beginning_listp; bp; bp = (void*)GET(NEXT_PTR(bp))) {
		
		if (!GET_ALLOC(HDRP(bp))) {
			if (asize == GET_SIZE(HDRP(bp))) {
				return (bp);
			}
			else if (GET_SIZE(HDRP(bp)) > asize && (!minimum_pointer || (GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(minimum_pointer))))) {
				minimum_pointer = bp;
			}
		}
	}
	/* No fit was found. */
	return (minimum_pointer);
}

/* 
 * Requires:
 *   "bp" is the address of a free block that is at least "asize" bytes.
 *
 * Effects:
 *   Place a block of "asize" bytes at the start of the free block "bp" and
 *   split that block if the remainder would be at least the minimum block
 *   size. 
 */
static void
place(void *bp, size_t asize)
{
	size_t csize = GET_SIZE(HDRP(bp));   
	uintptr_t prev_ptr = GET(PREV_PTR(bp));
	uintptr_t next_ptr = GET(NEXT_PTR(bp));

	if ((csize - asize) >= (5*WSIZE)) { 
		PUT(HDRP(bp), PACK(asize, 1));
		PUT(FTRP(bp), PACK(asize, 1));
		
		void* next_blk = NEXT_BLKP(bp);

		if (next_blk) {
			PUT(HDRP(next_blk), PACK(csize - asize, 0));
			PUT(FTRP(next_blk), PACK(csize - asize, 0));
		}
		if (prev_ptr) {
			PUT(NEXT_PTR(prev_ptr), (uintptr_t)next_blk);
			
			if (next_blk) {
				PUT(PREV_PTR(next_blk), prev_ptr); 
				PUT(NEXT_PTR(next_blk), next_ptr);
				if (next_ptr) {
					PUT(PREV_PTR(next_ptr), (uintptr_t)next_blk);
				}
			}
			//printf("1\n");
		}
		else if (bp == (void*)beginning_listp) {

			if (next_blk) {
				PUT(PREV_PTR(next_blk), 0); 	
				PUT(NEXT_PTR(next_blk), next_ptr); // Redundant??
				beginning_listp = (uintptr_t)next_blk;							
				if (next_ptr) {
					PUT(PREV_PTR(next_ptr), (uintptr_t) next_blk);
				}
			}
			else {
				if (next_ptr) {
					PUT(PREV_PTR(next_ptr), 0);
				}
				beginning_listp = (uintptr_t)next_ptr;								
			}
		//	printf("2\n");
		}
		else {
			printf("error1\n");
		}
				
		
	} else {
		
		if (prev_ptr) {
			PUT(NEXT_PTR(prev_ptr), (uintptr_t)next_ptr);
			if (next_ptr) {
				PUT(PREV_PTR(next_ptr), prev_ptr); 
			}
			//printf("3\n");

		}	
		else if (bp == (void*)beginning_listp) {
			
			beginning_listp = (uintptr_t)next_ptr;
			if (next_ptr) {
				PUT(PREV_PTR((void *)next_ptr), (uintptr_t)0); 	
			}			
			//printf("4\n");
  
		}
		else {
			printf("error2\n");
		}
		PUT(HDRP(bp), PACK(csize, 1));
		PUT(FTRP(bp), PACK(csize, 1));
				
	}
}

/* 
 * The remaining routines are heap consistency checker routines. 
 */

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Perform a minimal check on the block "bp".
 */
static void
checkblock(void *bp) 
{

	if ((uintptr_t)bp % WSIZE)
		printf("Error: %p is not doubleword aligned\n", bp);
	if (GET(HDRP(bp)) != GET(FTRP(bp)))
		printf("Error: header does not match footer\n");
}

/* 
 * Requires:
 *   None.
 *
 * Effects:
 *   Perform a minimal check of the heap for consistency. 
 */
void
checkheap(bool verbose) 
{
	void *bp;

	//printf("%ul\n", GET_SIZE(HDRP(heap_listp)));
	if (verbose)
		printf("Heap (%p):\n", heap_listp);

	if (GET_SIZE(HDRP(heap_listp)) != WSIZE ||
	    !GET_ALLOC(HDRP(heap_listp)))
		printf("Bad prologue header\n");
	checkblock(heap_listp);

	for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
		if (verbose)
			printblock(bp);
		checkblock(bp);
	}

	if (verbose)
		printblock(bp);
	if (GET_SIZE(HDRP(bp)) != 0 || !GET_ALLOC(HDRP(bp))) {
		printf("Epilogue %p\n", bp);
		printf("Bad epilogue header\n");
	}
}

/*
 * Requires:
 *   "bp" is the address of a block.
 *
 * Effects:
 *   Print the block "bp".
 */
static void
printblock(void *bp) 
{
	bool halloc, falloc;
	size_t hsize, fsize;

	checkheap(false);
	hsize = GET_SIZE(HDRP(bp));
	halloc = GET_ALLOC(HDRP(bp));  
	fsize = GET_SIZE(FTRP(bp));
	falloc = GET_ALLOC(FTRP(bp));  

	if (hsize == 0) {
		printf("%p: end of heap\n", bp);
		return;
	}

	printf("%p: header: [%zu:%c] footer: [%zu:%c]\n", bp, 
	    hsize, (halloc ? 'a' : 'f'), 
	    fsize, (falloc ? 'a' : 'f'));
}
