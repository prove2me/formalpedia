-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_original_large_negative_mark_finite_Levy_generator_compensator_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:28:51.785637+00:00
-- url     : https://prove2.me/submissions/8e27a806-3e4e-4153-b578-e5890ffd9657

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z ∂X.ν) =
    -(1 + y + y ^ 2) * (X.ν (Iio (0 : ℝ))).toReal := by
  have hAE : ∀ᵐ z ∂(X.ν.restrict (Iio (0 : ℝ))),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
        y z = -(1 + y + y ^ 2) := by
    filter_upwards [hSupport] with z hz
    have hNeg : y + z < 0 := by linarith
    have hPos : ¬ y < 0 := not_lt_of_ge hy
    have hSmall : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hh
      linarith [hh.1]
    simp [SpectrallyNegativeLevy.generatorIntegrand, hNeg, hPos, hSmall]
  have hEq :
      (∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand
          (fun u : ℝ => if u < 0 then 0 else 1 + u + u ^ 2)
          y z ∂X.ν) =
      (∫ _z in Iio (0 : ℝ), -(1 + y + y ^ 2) ∂X.ν) :=
    integral_congr_ae hAE
  rw [hEq]
  simp [integral_const, hFinite, mul_comm]
  all_goals first | exact Or.inl rfl | simp [Measure.real] | ring
