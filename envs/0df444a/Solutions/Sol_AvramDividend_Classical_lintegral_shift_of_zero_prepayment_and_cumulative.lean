-- Prove2me | solution 1 for AvramDividend.Classical.lintegral_shift_of_zero_prepayment_and_cumulative
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T18:40:50.770746+00:00
-- url     : https://prove2.me/submissions/2aed125d-d9dd-4bef-8819-4a26564d33fd

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_measure_eq_translated_of_zero_prepayment_and_cumulative

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical
theorem solution
    (μ ν : Measure ℝ) [IsLocallyFiniteMeasure μ] (u : ℝ)
    (hμzero : μ (Set.Iic u) = 0)
    (hνzero : ν (Set.Iic (0 : ℝ)) = 0)
    (hcum : ∀ t : ℝ, 0 ≤ t →
      μ (Set.Ioc u (u + t)) = ν (Set.Ioc (0 : ℝ) t))
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t : ℝ, f t ∂μ) =
      ∫⁻ t : ℝ, f (u + t) ∂ν := by
  rw [AvramDividend.Classical.measure_eq_translated_of_zero_prepayment_and_cumulative μ ν u hμzero hνzero hcum,
    lintegral_map hf (measurable_const_add u)]
