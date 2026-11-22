-- Prove2me | solution 1 for GJKKL.History.prob_not_alive_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:26:58.422522+00:00
-- url     : https://prove2.me/submissions/07d92920-e9ad-45c1-831b-ed698002f79e

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
public import Theorems.Thm_GJKKL_History_sum_K_mul_le
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_mono
public import Theorems.Thm_GJKKL_History_expect_succ
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_prob_or_le
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_weight_nil
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
theorem _root_.solution (T : ℕ) :
    prob κ T (fun h => ¬ AliveBefore G h) ≤
      ∑ i ∈ range T, prob κ i (fun h => AliveBefore G h ∧ ¬ G h) := by
  classical
  induction T with
  | zero =>
    unfold prob
    simp
  | succ T ih =>
    rw [sum_range_succ]
    have hsplit : prob κ (T + 1) (fun h => ¬ AliveBefore G h) ≤
        prob κ T (fun h => ¬ AliveBefore G h) +
          prob κ T (fun h => AliveBefore G h ∧ ¬ G h) := by
      refine le_trans ?_ (prob_or_le κ T _ _)
      unfold prob
      rw [expect_succ]
      refine expect_mono κ fun h _ => ?_
      refine sum_K_mul_le κ h (fun a => ?_) (by split_ifs <;> norm_num)
      by_cases h1 : AliveBefore G h <;> by_cases h2 : G h <;> simp [h1, h2]
    linarith
end GJKKL.History
