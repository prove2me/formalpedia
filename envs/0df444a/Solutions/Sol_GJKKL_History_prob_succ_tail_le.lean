-- Prove2me | solution 1 for GJKKL.History.prob_succ_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:57.604827+00:00
-- url     : https://prove2.me/submissions/496aca4f-b18f-4f8c-888b-b3e66791c92c

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
public import Theorems.Thm_GJKKL_History_sum_K_mul_le
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_mono
public import Theorems.Thm_GJKKL_History_expect_succ
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_Pseudorandom_CoordGap_tail
public import Theorems.Thm_Pseudorandom_CoordRare_tail
public import Theorems.Thm_Pseudorandom_IsPMF_tail
attribute [local simp] GJKKL.History.aliveBefore_cons
attribute [local simp] GJKKL.History.aliveBefore_nil
attribute [local simp] GJKKL.History.expect_zero
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.weight_nil



set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α] (κ : Kernel α) (G : List α → Prop)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (E : List α → Prop) :
    prob κ (T + 1) (fun h => E h.tail) ≤ prob κ T E := by
  classical
  unfold prob
  rw [expect_succ]
  refine expect_mono κ fun h _ => ?_
  refine sum_K_mul_le κ h (fun a => ?_) (by split_ifs <;> norm_num)
  by_cases hE : E h <;> simp [hE]
end GJKKL.History
