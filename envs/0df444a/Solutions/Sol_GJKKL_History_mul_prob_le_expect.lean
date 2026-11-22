-- Prove2me | solution 1 for GJKKL.History.mul_prob_le_expect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:02:05.008146+00:00
-- url     : https://prove2.me/submissions/1e3893d3-a196-4044-a79d-f4ee9b26d717

module
public import Mathlib
public import Definitions.Def_GJKKL_History_Basic
public import Theorems.Thm_GJKKL_History_expect_mono
public import Theorems.Thm_GJKKL_History_expect_const_mul

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α)
namespace GJKKL.History
theorem _root_.solution {T : ℕ} {P : List α → Prop} {Z : List α → ℝ} {c : ℝ}
    (hZ : ∀ h, h.length = T → 0 ≤ Z h) (hcZ : ∀ h, h.length = T → P h → c ≤ Z h) :
    c * prob κ T P ≤ expect κ T Z := by
  classical
  unfold prob
  rw [← expect_const_mul]
  refine expect_mono κ fun h hh => ?_
  split_ifs with hP
  · rw [mul_one]; exact hcZ h hh hP
  · rw [mul_zero]; exact hZ h hh
end GJKKL.History
