-- Prove2me | solution 2 for AvramDividend.Classical.paymentTimes_lintegral_smul_volume
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:17:22.112517+00:00
-- url     : https://prove2.me/submissions/70a48f1d-2604-4503-9734-502c9586ca83

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
