-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_time_reversal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T21:50:09.504061+00:00
-- url     : https://prove2.me/submissions/1475d420-582e-44af-86c3-21450778a730

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K g : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in Ioc (0 : ℝ) t, K (t - s) * g s ∂volume) =
    (∫ u in Ioc (0 : ℝ) t, K u * g (t - u) ∂volume) := by
  calc
    _ = ∫ s in (0 : ℝ)..t,
      (fun u : ℝ => K u * g (t - u)) (t - s) := by
        rw [intervalIntegral.integral_of_le ht]
        simp only [sub_sub_cancel]
    _ = ∫ u in (t - t)..(t - 0),
      K u * g (t - u) := by
        exact intervalIntegral.integral_comp_sub_left
          (fun u : ℝ => K u * g (t - u)) t
    _ = _ := by
      simpa [sub_self, sub_zero, intervalIntegral.integral_of_le ht]
