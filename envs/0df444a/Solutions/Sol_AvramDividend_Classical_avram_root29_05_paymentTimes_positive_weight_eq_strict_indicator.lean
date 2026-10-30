-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_paymentTimes_positive_weight_eq_strict_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:51:10.899985+00:00
-- url     : https://prove2.me/submissions/d12b82c0-35f2-475f-8c32-e5bc3e333271

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal Classical

/-- The exact original stopped payment-set integral of positive-time dividends
equals its full-time strict ruin indicator, while time zero contributes zero. -/
theorem solution (μ : Measure ℝ) (q : ℝ) (τ : ℝ≥0∞) :
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) =
    (∫⁻ r : ℝ,
      if 0 < r then
        if ENNReal.ofReal r < τ then
          ENNReal.ofReal (Real.exp (-(q * r))) else 0
      else 0 ∂μ) := by
  rw [← lintegral_indicator (paymentTimes_measurable τ)]
  apply lintegral_congr
  intro r
  by_cases hp : 0 < r
  · have hn : r ≠ 0 := ne_of_gt hp
    simp [Set.indicator, paymentTimes, hp, hp.le, hn]
  · simp [Set.indicator, hp]
