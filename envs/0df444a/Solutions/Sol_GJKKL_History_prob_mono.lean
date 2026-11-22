-- Prove2me | solution 1 for GJKKL.History.prob_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:01.129366+00:00
-- url     : https://prove2.me/submissions/de7eedec-e9cf-4fcd-a162-a18ea1eb9393

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_expect_mono

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution {T : ℕ} {P Q : List α → Prop} (hPQ : ∀ h, h.length = T → P h → Q h) :
    prob κ T P ≤ prob κ T Q := by
  classical
  unfold prob
  refine expect_mono κ fun h hh => ?_
  by_cases hP : P h
  · rw [if_pos hP, if_pos (hPQ h hh hP)]
  · rw [if_neg hP]; split_ifs <;> norm_num
end GJKKL.History
