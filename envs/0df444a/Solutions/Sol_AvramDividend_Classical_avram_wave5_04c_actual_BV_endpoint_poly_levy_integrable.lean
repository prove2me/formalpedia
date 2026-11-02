-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_actual_BV_endpoint_poly_levy_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:38:12.533539+00:00
-- url     : https://prove2.me/submissions/fa2895ee-e36b-4158-b6e6-22853387fb79

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! BV-integrability of arbitrary endpoint-zero exponential polynomial
against the true negative Levy measure, even with infinite activity. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (Q : Polynomial ℝ) (hQ : Polynomial.eval 1 Q = 0) :
    IntegrableOn (fun y : ℝ => Polynomial.eval (Real.exp y) Q)
      (Iio (0 : ℝ)) X.ν := by
  obtain ⟨p, hp0, hpR⟩ :=
    avram_wave5_04c_endpoint_zero_poly_as_exponential_primitive Q hQ
  have hInt :=
    avram_wave5_04c_actual_bv_zero_poly_primitive_levy_integrable
      X hBV p hp0
  have heq : (fun y : ℝ =>
      ∫ r in (0 : ℝ)..(-y),
        Polynomial.eval (Real.exp (-r)) p) =ᵐ[X.ν.restrict (Iio (0 : ℝ))]
      (fun y : ℝ => Polynomial.eval (Real.exp y) Q) := by
    filter_upwards with y
    simpa only [neg_neg] using (hpR (-y))
  exact hInt.congr heq
