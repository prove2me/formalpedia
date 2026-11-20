-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_finite_activity_generator_negative_jump_integral_floor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:51:47.239539+00:00
-- url     : https://prove2.me/submissions/c3e56028-b9e4-4997-b55f-8928aff9217f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_negative_jump_generator_integrand_pointwise_floor
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hνFin : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (hwpos : ∀ u : ℝ, 0 ≤ w u)
    (y : ℝ) (hderiv : 0 ≤ deriv w y)
    (hGen : X.GeneratorIntegrable w y) :
    -(X.ν (Iio (0 : ℝ))).toReal * w y ≤
      ∫ z in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hνFin⟩
  have hConst : Integrable (fun _ : ℝ => -w y) μ := integrable_const _
  have hInt : Integrable
      (fun z => SpectrallyNegativeLevy.generatorIntegrand w y z) μ := hGen
  have hFloor :
      (∀ᵐ z : ℝ ∂μ,
        -w y ≤ SpectrallyNegativeLevy.generatorIntegrand w y z) := by
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    exact avram_f6_original_negative_jump_generator_integrand_pointwise_floor
      w y z hwpos hderiv hz
  have hMono :
      ∫ z, (-w y) ∂μ ≤
        ∫ z, SpectrallyNegativeLevy.generatorIntegrand w y z ∂μ :=
    integral_mono_ae hConst hInt hFloor
  calc
    -(X.ν (Iio (0 : ℝ))).toReal * w y =
        (μ Set.univ).toReal * (-w y) := by
          simp [μ, mul_comm, mul_left_comm]
    _ = ∫ z, (-w y) ∂μ := by simp [integral_const, Measure.real, mul_comm]
    _ ≤ ∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
            exact hMono
