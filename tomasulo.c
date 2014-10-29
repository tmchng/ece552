
#include <limits.h>
#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "host.h"
#include "misc.h"
#include "machine.h"
#include "regs.h"
#include "memory.h"
#include "loader.h"
#include "syscall.h"
#include "dlite.h"
#include "options.h"
#include "stats.h"
#include "sim.h"
#include "decode.def"

#include "instr.h"

/* PARAMETERS OF THE TOMASULO'S ALGORITHM */

#define INSTR_QUEUE_SIZE         10

#define RESERV_INT_SIZE    4
#define RESERV_FP_SIZE     2
#define FU_INT_SIZE        2
#define FU_FP_SIZE         1

#define FU_INT_LATENCY     4
#define FU_FP_LATENCY      9

/* IDENTIFYING INSTRUCTIONS */

//unconditional branch, jump or call
#define IS_UNCOND_CTRL(op) (MD_OP_FLAGS(op) & F_CALL || \
                         MD_OP_FLAGS(op) & F_UNCOND)

//conditional branch instruction
#define IS_COND_CTRL(op) (MD_OP_FLAGS(op) & F_COND)

//floating-point computation
#define IS_FCOMP(op) (MD_OP_FLAGS(op) & F_FCOMP)

//integer computation
#define IS_ICOMP(op) (MD_OP_FLAGS(op) & F_ICOMP)

//load instruction
#define IS_LOAD(op)  (MD_OP_FLAGS(op) & F_LOAD)

//store instruction
#define IS_STORE(op) (MD_OP_FLAGS(op) & F_STORE)

//trap instruction
#define IS_TRAP(op) (MD_OP_FLAGS(op) & F_TRAP)

#define USES_INT_FU(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_STORE(op))
#define USES_FP_FU(op) (IS_FCOMP(op))

#define WRITES_CDB(op) (IS_ICOMP(op) || IS_LOAD(op) || IS_FCOMP(op))

/* FOR DEBUGGING */

//prints info about an instruction
#define PRINT_INST(out,instr,str,cycle)	\
  myfprintf(out, "%d: %s", cycle, str);		\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

#define PRINT_REG(out,reg,str,instr) \
  myfprintf(out, "reg#%d %s ", reg, str);	\
  md_print_insn(instr->inst, instr->pc, out); \
  myfprintf(stdout, "(%d)\n",instr->index);

/* VARIABLES */

//instruction queue for tomasulo
static instruction_t* instr_queue[INSTR_QUEUE_SIZE];
//number of instructions in the instruction queue
static int instr_queue_size = 0;

/* ECE552 Assignment 3 - BEGIN CODE */
// For keeping track of where the head and tail of the queue is.
static int instr_queue_start = 0;
// Number of instructions completed in simulation.
static int sim_insn_count = 0;
/* ECE552 Assignment 3 - END CODE */

//reservation stations (each reservation station entry contains a pointer to an instruction)
static instruction_t* reservINT[RESERV_INT_SIZE];
static instruction_t* reservFP[RESERV_FP_SIZE];

//functional units
static instruction_t* fuINT[FU_INT_SIZE];
static instruction_t* fuFP[FU_FP_SIZE];

//common data bus
static instruction_t* commonDataBus = NULL;

//The map table keeps track of which instruction produces the value for each register
static instruction_t* map_table[MD_TOTAL_REGS];

//the index of the last instruction fetched
/* ECE552 Assignment 3 - BEGIN CODE */
// Fetch index is zero-indexed.
static int fetch_index = 0;
/* ECE552 Assignment 3 - END CODE */

/* FUNCTIONAL UNITS */


/* RESERVATION STATIONS */


/*
 * Description:
 * 	Checks if simulation is done by finishing the very last instruction
 *      Remember that simulation is done only if the entire pipeline is empty
 * Inputs:
 * 	sim_insn: the total number of instructions simulated
 * Returns:
 * 	True: if simulation is finished
 */
static bool is_simulation_done(counter_t sim_insn) {

  /* ECE552: YOUR CODE GOES HERE */
  return sim_insn >= 100;
}

/*
 * Description:
 * 	Retires the instruction from writing to the Common Data Bus
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void CDB_To_retire(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
	int i, j;
	instruction_t *instr = commonDataBus;
	// fp_bool => if 1, instr in the CDB is a FP inst
	// instr => insn pointer
	// rs_index => index of insn in RS
	// fu_index => index of insn in FU
	// cycle_fetched => used to compare multiple insn, to check which was fetched first

	if (instr != NULL){
		//printf("retiring %p\n", instr);
		// broadcast complete. this is shown as freeing the RS/maptable/FU/CDB
		for (i = 0;  i < RESERV_FP_SIZE; i++){
			if (instr == reservFP[i] && USES_FP_FU(instr->op)){
				reservFP[i] = NULL;
			}
			if (reservFP[i] != NULL){
				for (j = 0; j < 3; j ++){
					if (reservFP[i]->Q[j] == instr)// clear dependencies (resolve RAWs)
						reservFP[i]->Q[j] = NULL;
				}
			}
		}
		for (i = 0;  i < RESERV_INT_SIZE; i++){
			if (instr == reservINT[i] && USES_INT_FU(instr->op)){
				reservINT[i] = NULL;
			}
			if (reservINT[i] != NULL){
				for (j = 0; j < 3; j ++){
					if (reservINT[i]->Q[j] == instr)// clear dependencies (resolve RAWs)
						reservINT[i]->Q[j] = NULL;
				}
			}
		}
		commonDataBus = NULL;
		for (i = 0; i < FU_INT_SIZE && USES_INT_FU(instr->op); i++){
			if (instr == fuINT[i]){
				//printf("clear FU INT %d\n", i);
				fuINT[i] = NULL;
			}
		}
		for (i = 0; i < FU_FP_SIZE && USES_FP_FU(instr->op); i++){
			if (instr == fuFP[i]){
				//printf("clear FU FP %d\n", i);
				fuFP[i] = NULL;
			}
		}
		// clear map table
		for (i = 0; i < MD_TOTAL_REGS; i++){
			if (map_table[i] == instr){
				//printf("clear map %d\n", i);
				map_table[i] = NULL;
			}
		}
                sim_insn_count++;
	}
}


/*
 * Description:
 * 	Moves an instruction from the execution stage to common data bus (if possible)
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void execute_To_CDB(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  int i, j;
  // Num of intr that are completed and don't need CDB.
  int instr_completed = 0;
  instruction_t *completed[FU_INT_SIZE + FU_FP_SIZE];
  instruction_t *instr = NULL;
  instruction_t *old_instr = NULL;

  // Store does not need CDB
  // Figure out which instructions are completed.
  for (i = 0; i < FU_INT_SIZE; i++) {
    instr = fuINT[i];
    if (instr != NULL &&
        (current_cycle - instr->tom_execute_cycle) >= FU_INT_LATENCY) {
      if (WRITES_CDB(instr->op)) {
        assert(instr->tom_cdb_cycle <= 0);
        // We prioritize the oldest instruction first
        if (old_instr == NULL) {
          old_instr = instr;
        } else if (old_instr->index > instr->index) {
          old_instr = instr;
        }

      } else {
        // These instructions don't need CDB
        completed[instr_completed] = instr;
        instr_completed++;
      }
    }
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    instr = fuFP[i];
    if (instr != NULL &&
        (current_cycle - instr->tom_execute_cycle) >= FU_FP_LATENCY) {
      if (WRITES_CDB(instr->op)) {
        assert(instr->tom_cdb_cycle <= 0);
        // We prioritize the oldest instruction first
        if (old_instr == NULL) {
          old_instr = instr;
        } else if (old_instr->index > instr->index) {
          old_instr = instr;
        }

      } else {
        // These instructions don't need CDB
        completed[instr_completed] = instr;
        instr_completed++;
      }
    }
  }

  if (old_instr != NULL) {
    // Move the oldest completed instruction to CDB
    old_instr->tom_cdb_cycle = current_cycle;
    commonDataBus = old_instr;
    // Retire will handle deallocate RS and FU for instruction
    // that needs CDB.
  }

  // For every completed instructions that don't need CDB,
  // deallocate RS and FU
  for (i = 0; i < instr_completed; i++) {
    instr = completed[i];
    sim_insn_count++;
    if (USES_FP_FU(instr->op)) {
      for (j = 0; j < FU_FP_SIZE; j++) {
        if (fuFP[j] == instr) {
          fuFP[j] = NULL;
          break;
        }
      }
      for (j = 0; j < RESERV_FP_SIZE; j++) {
        if (reservFP[j] == instr) {
          reservFP[j] = NULL;
          break;
        }
      }

    } else if (USES_INT_FU(instr->op)) {
      for (j = 0; j < FU_INT_SIZE; j++) {
        if (fuINT[j] == instr) {
          fuINT[j] = NULL;
          break;
        }
      }
      for (j = 0; j < RESERV_INT_SIZE; j++) {
        if (reservINT[j] == instr) {
          reservINT[j] = NULL;
          break;
        }
      }
    }
  }
}

/*
 * Description:
 * 	Moves instruction(s) from the issue to the execute stage (if possible). We prioritize old instructions
 *      (in program order) over new ones, if they both contend for the same functional unit.
 *      All RAW dependences need to have been resolved with stalls before an instruction enters execute.
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void issue_To_execute(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  int i, j, k;
  int freeFuINT = 0;
  int freeFuINTi[FU_INT_SIZE];
  int freeFuFP = 0;
  int freeFuFPi[FU_FP_SIZE];

  int ready;
  instruction_t *instr = NULL;
  instruction_t *old_instr = NULL;

  // Count number of free INT FU's.
  for (i = 0; i < FU_INT_SIZE; i++) {
    if (fuINT[i] == NULL) {
      freeFuINTi[freeFuINT] = i;
      freeFuINT++;
    }
  }
  // Count number of free FP FU's.
  for (i = 0; i < FU_FP_SIZE; i++) {
    if (fuFP[i] == NULL) {
      freeFuFPi[freeFuFP] = i;
      freeFuFP++;
    }
  }

  while (freeFuINT > 0) {
    // Get the oldest instruction from reservINT
    old_instr = NULL;
    for (j = 0; j < RESERV_INT_SIZE; j++) {
      instr = reservINT[j];
      if (instr == NULL) continue;
      if (instr->tom_execute_cycle > 0) continue; // Issued.

      // Check if instruction is ready to execute.
      ready = 1;
      for (k = 0; k < 3; k++) {
        if (instr->Q[k] != NULL) {
          // One of the input is not ready.
          ready = 0;
          break;
        }
      }

      if (ready) {
        // Prioritize older instructions first
        if (old_instr == NULL) {
          old_instr = instr;
        } else if (old_instr->index > instr->index){
          // Replace with older instruction
          old_instr = instr;
        }
      }
    }

    if (old_instr == NULL) {
      // There's no instruction in the RS.
      break;
    }

    // Execute the oldest instruction.
    old_instr->tom_execute_cycle = current_cycle;
	//printf("execute %p\n", old_instr);
    // Reserve the functional unit.
    fuINT[freeFuINTi[freeFuINT-1]] = old_instr;
    freeFuINT--;
  }

  while (freeFuFP > 0) {
    // Get the oldest instruction from reservFP
    old_instr = NULL;
    for (j = 0; j < RESERV_FP_SIZE; j++) {
      instr = reservFP[j];
      if (instr == NULL) continue;
      if (instr->tom_execute_cycle > 0) continue; // Issued.

      // Check if instruction is ready to execute.
      ready = 1;
      for (k = 0; k < 3; k++) {
        if (instr->Q[k] != NULL) {
          // One of the input is not ready.
          ready = 0;
          break;
        }
      }

      if (ready) {
        // Prioritize older instructions first
        if (old_instr == NULL) {
          old_instr = instr;
        } else if (old_instr->index > instr->index){
          // Replace with older instruction
          old_instr = instr;
        }
      }
    }

    if (old_instr == NULL) {
      // There's no instruction in the RS.
      break;
    }

    // Execute the oldest instruction.
    old_instr->tom_execute_cycle = current_cycle;
	//printf("execute %p\n", old_instr);

    // Reserve the functional unit.
    fuFP[freeFuFPi[freeFuFP-1]] = old_instr;
    freeFuFP--;
  }
}

/*
 * Description:
 * 	Moves instruction(s) from the dispatch stage to the issue stage
 * Inputs:
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void dispatch_To_issue(int current_cycle) {

  /* ECE552: YOUR CODE GOES HERE */
  if (instr_queue_size <= 0) return;

  int j, reg_num;
  int issue = 0;
  instruction_t *instr = NULL;

  while (instr_queue_size > 0) {
    instr = instr_queue[instr_queue_start];
    if (instr == NULL) {
      // If the first instr is null then the queue is empty.
      return;
    }

    if (IS_COND_CTRL(instr->op) || IS_UNCOND_CTRL(instr->op)) {
      // Jump and branch can dispatch right away.
      instr->tom_issue_cycle = current_cycle;
      // Simply remove from instr queue.
      instr_queue[instr_queue_start] = NULL;
      instr_queue_start = (instr_queue_start + 1) % INSTR_QUEUE_SIZE;
      instr_queue_size--;
      continue;

    } else if (USES_INT_FU(instr->op)) {
      // Find available reservation station.
      for (j = 0; reservINT[j] != NULL; j++) {}
      if (j < RESERV_INT_SIZE) {
        reservINT[j] = instr;
        issue = 1;
      }

    } else if (USES_FP_FU(instr->op)) {
      // Find available reservation station.
      for (j = 0; reservFP[j] != NULL; j++) {}
      if (j < RESERV_FP_SIZE) {
        reservFP[j] = instr;
        issue = 1;
      }
    }

    if (issue) {
      instr->tom_issue_cycle = current_cycle;

      // Collect input values/tags first
      for (j = 0; j < 3; j++) {
        reg_num = instr->r_in[j];
        if (reg_num != 0 && map_table[reg_num] != NULL) {
          // Map table indicates that an input reg is not ready.
          instr->Q[j] = map_table[reg_num];
        }
      }

      // Update the map table with output reg
      for (j = 0; j < 2; j++) {
        reg_num = instr->r_out[j];
        if (reg_num != 0) {
          map_table[reg_num] = instr;
        }
      }

      // Remove instr from queue.
      instr_queue[instr_queue_start] = NULL;
      instr_queue_start = (instr_queue_start + 1) % INSTR_QUEUE_SIZE;
      instr_queue_size--;

    } else {
      // Cannot go from dispatch to issue out of order.
      return;
    }
  }
}

/*
 * Description:
 * 	Grabs an instruction from the instruction trace (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	None
 */
void fetch(instruction_trace_t* trace) {

  /* ECE552: YOUR CODE GOES HERE */
  instruction_t *new_instr = NULL;

  if (instr_queue_size < INSTR_QUEUE_SIZE) {

    // Fetch ONE instruction
    // Fetch index starts from 1
    fetch_index++;
    new_instr = get_instr(trace, fetch_index);

    // Skip TRAP instructions
    while (new_instr != NULL && IS_TRAP(new_instr->op)) {
      fetch_index++;
      new_instr = get_instr(trace, fetch_index);
    }

    if (new_instr != NULL) {
      // Put instruction in end of queue
      int queue_end = (instr_queue_start + instr_queue_size) % INSTR_QUEUE_SIZE;
      instr_queue[queue_end] = new_instr;
      instr_queue_size++;
	//printf("instr %p\n", new_instr);
    }
  }
}




/*
 * Description:
 * 	Calls fetch and dispatches an instruction at the same cycle (if possible)
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * 	current_cycle: the cycle we are at
 * Returns:
 * 	None
 */
void fetch_To_dispatch(instruction_trace_t* trace, int current_cycle) {

  fetch(trace);

  /* ECE552: YOUR CODE GOES HERE */
  if (instr_queue_size == 0) return;

  // Since we only dispatch one instruction at a time, we only need to look
  // at the last thing in the queue.
  int queue_end = (instr_queue_start + instr_queue_size - 1) % INSTR_QUEUE_SIZE;
  instruction_t *instr = instr_queue[queue_end];
  if (instr != NULL && instr->tom_dispatch_cycle <= 0) {
    instr->tom_dispatch_cycle = current_cycle;
  }
}

/*
 * Description:
 * 	Performs a cycle-by-cycle simulation of the 4-stage pipeline
 * Inputs:
 *      trace: instruction trace with all the instructions executed
 * Returns:
 * 	The total number of cycles it takes to execute the instructions.
 * Extra Notes:
 * 	sim_num_insn: the number of instructions in the trace
 */
counter_t runTomasulo(instruction_trace_t* trace)
{
  //initialize instruction queue
  int i;
  for (i = 0; i < INSTR_QUEUE_SIZE; i++) {
    instr_queue[i] = NULL;
  }

  //initialize reservation stations
  for (i = 0; i < RESERV_INT_SIZE; i++) {
      reservINT[i] = NULL;
  }

  for(i = 0; i < RESERV_FP_SIZE; i++) {
      reservFP[i] = NULL;
  }

  //initialize functional units
  for (i = 0; i < FU_INT_SIZE; i++) {
    fuINT[i] = NULL;
  }

  for (i = 0; i < FU_FP_SIZE; i++) {
    fuFP[i] = NULL;
  }

  //initialize map_table to no producers
  int reg;
  for (reg = 0; reg < MD_TOTAL_REGS; reg++) {
    map_table[reg] = NULL;
  }

  int cycle = 1;
  while (true) {

     /* ECE552: YOUR CODE GOES HERE */

	CDB_To_retire(cycle);
	execute_To_CDB(cycle);
	issue_To_execute(cycle);
	dispatch_To_issue(cycle);
	fetch_To_dispatch(trace ,cycle);

	cycle++;
        if (is_simulation_done(sim_insn_count) || cycle >= 10000000) {
          print_all_instr(trace, sim_num_insn);
          break;

        }
  }

  return cycle;
}
