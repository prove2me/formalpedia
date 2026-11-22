-- Prove2me | solution 1 for GJKKL.sum_dv_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:07:37.850928+00:00
-- url     : https://prove2.me/submissions/ff695b1a-da7f-4e6a-9d3e-c481b21e5eba

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_Greedy_Degrees
public import Theorems.Thm_GJKKL_Dv_nil
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_isGreedySeq_cons
public import Theorems.Thm_GJKKL_isGreedySeq_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.isGreedySeq_cons
attribute [local simp] GJKKL.isGreedySeq_nil


attribute [local simp] GJKKL.Dv_nil

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution (H : Finset (Finset V)) (h : List (Finset V)) :
    ∑ v, dv H h v = ∑ e ∈ avail H h, e.card := by
  simp only [dv, Dv, card_filter]
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  rw [← card_filter, filter_mem_eq_inter, univ_inter]
end GJKKL
