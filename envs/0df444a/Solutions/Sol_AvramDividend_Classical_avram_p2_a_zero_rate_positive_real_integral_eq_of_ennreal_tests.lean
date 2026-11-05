-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_positive_real_integral_eq_of_ennreal_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:51:43.259191+00:00
-- url     : https://prove2.me/submissions/3a5d7758-d7f7-4ade-b527-8480ffe68654

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal

/-- Nonnegative real integral determined by the ENNReal moment. -/
theorem solution
    {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (f : α → ℝ)
    (hf : ∀ x : α, 0 ≤ f x)
    (hμ : Integrable f μ) (hν : Integrable f ν)
    (hlin : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (f x) ∂ν)) :
    (∫ x, f x ∂μ) = (∫ x, f x ∂ν) := by
  have hAEμ : ∀ᵐ x ∂μ, (0 : ℝ) ≤ f x :=
    Filter.Eventually.of_forall hf
  have hAEν : ∀ᵐ x ∂ν, (0 : ℝ) ≤ f x :=
    Filter.Eventually.of_forall hf
  have hμcast := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hμ hAEμ
  have hνcast := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hν hAEν
  have hpμ : 0 ≤ (∫ x, f x ∂μ) :=
    MeasureTheory.integral_nonneg hf
  have hpν : 0 ≤ (∫ x, f x ∂ν) :=
    MeasureTheory.integral_nonneg hf
  apply (ENNReal.ofReal_eq_ofReal_iff hpμ hpν).mp
  calc
    ENNReal.ofReal (∫ x, f x ∂μ) =
        (∫⁻ x, ENNReal.ofReal (f x) ∂μ) := hμcast
    _ = (∫⁻ x, ENNReal.ofReal (f x) ∂ν) := hlin
    _ = ENNReal.ofReal (∫ x, f x ∂ν) := hνcast.symm
