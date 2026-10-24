-- Prove2me | solution 1 for AvramDividend.Classical.causal_reversed_kernel_right_interval_mass_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:21:13.965575+00:00
-- url     : https://prove2.me/submissions/34fee422-ef0f-4a80-9f1c-e4217d7a6af2

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Reflecting the right causal integration interval gives an ordinary truncated mass. -/
theorem solution
    (κ : ℝ → ℝ) (x u : ℝ) :
    (∫ s in u..x, κ (x - s)) =
      ∫ t in (0 : ℝ)..(x - u), κ t := by
  simpa only [sub_self] using
    (intervalIntegral.integral_comp_sub_left (a := u) (b := x) κ x)
