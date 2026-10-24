-- Prove2me | solution 1 for AvramDividend.Classical.excursion_laplace_lintegral_eq_on_supported_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T20:51:25.23335+00:00
-- url     : https://prove2.me/submissions/28b328c0-9254-4656-9872-210f0b6021ab

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-!
A measure supported on the nonnegative half-line integrates the capped
bounded Laplace test exactly as the ordinary exponential kernel.
-/
theorem solution (μ : Measure ℝ) (s : ℝ)
    (hsupport : μ (Iio (0 : ℝ)) = 0) :
    (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * max x 0))) ∂μ) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂μ) := by
  apply lintegral_congr_ae
  have hnonneg : ∀ᵐ x : ℝ ∂μ, 0 ≤ x := by
    have hnotmem := (measure_eq_zero_iff_ae_notMem).mp hsupport
    filter_upwards [hnotmem] with x hx
    exact le_of_not_gt hx
  filter_upwards [hnonneg] with x hx
  rw [max_eq_left hx]
