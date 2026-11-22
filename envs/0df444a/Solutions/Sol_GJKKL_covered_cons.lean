-- Prove2me | solution 1 for GJKKL.covered_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:43:03.61281+00:00
-- url     : https://prove2.me/submissions/65f31231-37fb-43e1-8a09-21ce97fdd5a7

module
public import Definitions.Def_GJKKL_Greedy_Drift
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Trajectory_Frozen
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
public import Theorems.Thm_GJKKL_mem_covered
attribute [local simp] GJKKL.Dv_nil
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (a : Finset V) (h : List (Finset V)) :
    covered (a :: h) = a ∪ covered h := by
  ext x; simp [mem_covered]
end GJKKL
