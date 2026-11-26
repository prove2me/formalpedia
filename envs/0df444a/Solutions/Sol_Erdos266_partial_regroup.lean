-- Prove2me | solution 1 for Erdos266.partial_regroup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:25.735541+00:00
-- url     : https://prove2.me/submissions/b80c4c3f-4581-4bbf-8dde-2a8d87ce24d9

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
public import Theorems.Thm_Erdos266_aSeq_block
public import Theorems.Thm_Erdos266_finSum_succ


set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology
namespace Erdos266
theorem _root_.solution (i' k : ℕ) :
    ∑ n ∈ range (cnt k), f (i' + 1) ((aSeq n : ℕ) : ℝ) = finSum i' k Sinf := by
  induction k with
  | zero => simp [cnt, finSum]
  | succ k ih =>
    rw [cnt_succ, sum_range_add, ih, finSum_succ]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    rw [aSeq_block (mem_range.mp hj)]
end Erdos266
