-- Prove2me | solution 1 for AvramDividend.Classical.causal_interval_translation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:17:03.371989+00:00
-- url     : https://prove2.me/submissions/e9ea0d73-8686-47a7-b253-14136de55ead

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Translating a causal subinterval gives an integral based at zero. -/
theorem solution
    (g : ℝ → ℝ) (u x : ℝ) (hux : u ≤ x) :
    (∫ t in Ioc u x, g (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by
  rw [← intervalIntegral.integral_of_le hux,
    ← intervalIntegral.integral_of_le (sub_nonneg.mpr hux)]
  simpa only [sub_self] using
    (intervalIntegral.integral_comp_sub_right
      (f := g) (d := u) (a := u) (b := x))
