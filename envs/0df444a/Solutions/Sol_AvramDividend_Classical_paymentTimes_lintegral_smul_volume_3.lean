-- Prove2me | solution 3 for AvramDividend.Classical.paymentTimes_lintegral_smul_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:17:34.04743+00:00
-- url     : https://prove2.me/submissions/4a68e73e-1c77-48fa-ba0b-ebd12aa24f2d

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    (σ : ℝ≥0∞) (c : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ t in paymentTimes σ, w t ∂(c • volume)) =
    (∫⁻ t in paymentTimes σ, c * w t ∂volume) := by
  rw [Measure.restrict_smul, lintegral_smul_measure, lintegral_const_mul _ hw, smul_eq_mul]
