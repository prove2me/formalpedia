-- Prove2me | solution 1 for AvramDividend.Classical.causal_shift_window_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:14:00.358221+00:00
-- url     : https://prove2.me/submissions/d3eb3eb9-9e05-484a-97fc-d0e1e0ab1c32

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (g : ℝ → ℝ) (u x : ℝ) (hux : u ≤ x) :
    (∫ t in Ioc u x, g (t - u) ∂volume) =
    (∫ s in Ioc (0 : ℝ) (x - u), g s ∂volume) := by
  calc
    _ = ∫ t in u..x, g (t - u) := by
      rw [intervalIntegral.integral_of_le hux]
    _ = ∫ s in (u - u)..(x - u), g s :=
      intervalIntegral.integral_comp_sub_right g u
    _ = _ := by
      simpa [sub_self, intervalIntegral.integral_of_le
        (sub_nonneg.mpr hux)]
