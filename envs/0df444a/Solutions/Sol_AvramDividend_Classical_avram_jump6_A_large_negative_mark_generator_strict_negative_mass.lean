-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_large_negative_mark_generator_strict_negative_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:33:37.32843+00:00
-- url     : https://prove2.me/submissions/fe9d286c-e642-4b34-8cea-5fe2a1835c6b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSupport : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))), z ≤ -2)
    (hMass : 0 < (X.ν (Iio (0 : ℝ))).toReal)
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z ∂X.ν) < 0 := by
  rw [avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
    X hFinite hSupport y hy hcap]
  have hp : 0 < 1 + y + y ^ 2 := by
    nlinarith [sq_nonneg y]
  nlinarith [mul_pos hp hMass]
