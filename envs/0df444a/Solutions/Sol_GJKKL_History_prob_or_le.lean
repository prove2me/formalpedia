-- Prove2me | solution 1 for GJKKL.History.prob_or_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:50.501685+00:00
-- url     : https://prove2.me/submissions/14657bb3-b0e4-4f20-bd97-b719d758a3d8

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_weight_nil
public import Theorems.Thm_GJKKL_History_weight_cons
public import Theorems.Thm_GJKKL_History_expect_zero
public import Theorems.Thm_GJKKL_History_expect_mono
public import Theorems.Thm_GJKKL_History_expect_add
attribute [local simp] GJKKL.History.weight_nil
attribute [local simp] GJKKL.History.weight_cons
attribute [local simp] GJKKL.History.expect_zero

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution (T : ℕ) (P Q : List α → Prop) :
    prob κ T (fun h => P h ∨ Q h) ≤ prob κ T P + prob κ T Q := by
  classical
  unfold prob
  rw [← expect_add]
  refine expect_mono κ fun h _ => ?_
  by_cases hP : P h <;> by_cases hQ : Q h <;> simp [hP, hQ]
end GJKKL.History
