-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite76_cash_error_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:01:03.473414+00:00
-- url     : https://prove2.me/submissions/5699154e-d423-4512-ab91-08529f7b4ac7

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Splitting a cash residual into its source term and its mesh remainder
    never increases the required positive-error budget. -/
theorem solution (a b c : ℝ) :
    max (a - c) 0 ≤ max (a - b) 0 + max (b - c) 0 := by
  have h₁ : a - b ≤ max (a - b) 0 := le_max_left _ _
  have h₂ : b - c ≤ max (b - c) 0 := le_max_left _ _
  have h₃ : (0 : ℝ) ≤ max (a - b) 0 := le_max_right _ _
  have h₄ : (0 : ℝ) ≤ max (b - c) 0 := le_max_right _ _
  apply max_le
  · linarith
  · linarith
