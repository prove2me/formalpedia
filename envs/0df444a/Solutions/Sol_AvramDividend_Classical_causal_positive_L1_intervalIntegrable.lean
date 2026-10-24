-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_L1_intervalIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:54:39.662257+00:00
-- url     : https://prove2.me/submissions/74a7b119-357b-4ac5-b646-546aaaaa6115

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Positive-axis L1 kernels are interval integrable on every finite positive horizon. -/
theorem solution
    (K : ℝ → ℝ) (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (x : ℝ) (hx : 0 < x) :
    IntervalIntegrable K volume 0 x := by
  rw [intervalIntegrable_iff, Set.uIoc_of_le hx.le]
  exact hK.mono_set (by
    intro y hy
    exact hy.1)
