-- Prove2me | solution 1 for GJKKL.History.prob_alive_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:05:27.446046+00:00
-- url     : https://prove2.me/submissions/8224455e-5f84-42e7-9620-7ae6113d375e

module
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_History_FirstFailure
public import Theorems.Thm_GJKKL_History_aliveBefore_cons
public import Theorems.Thm_GJKKL_History_aliveBefore_nil
public import Theorems.Thm_GJKKL_History_expect_add
public import Theorems.Thm_GJKKL_History_expect_congr
public import Theorems.Thm_GJKKL_History_expect_succ
public import Theorems.Thm_GJKKL_History_expect_zero
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
theorem _root_.solution (hmass : ∀ h, G h → ∑ a, κ.K h a = 1) (T : ℕ) :
    1 - ∑ i ∈ range T, prob κ i (fun h => AliveBefore G h ∧ ¬ G h) ≤
      prob κ T (AliveBefore G) := by
  classical
  induction T with
  | zero =>
    unfold prob
    simp
  | succ T ih =>
    rw [sum_range_succ]
    have hstep : prob κ (T + 1) (AliveBefore G) =
        prob κ T (AliveBefore G) - prob κ T (fun h => AliveBefore G h ∧ ¬ G h) := by
      unfold prob
      rw [expect_succ, eq_sub_iff_add_eq, ← expect_add]
      refine expect_congr κ fun h _ => ?_
      by_cases hal : AliveBefore G h
      · by_cases hG : G h
        · simp [hal, hG, hmass h hG]
        · simp [hal, hG]
      · simp [hal]
    linarith
end GJKKL.History
