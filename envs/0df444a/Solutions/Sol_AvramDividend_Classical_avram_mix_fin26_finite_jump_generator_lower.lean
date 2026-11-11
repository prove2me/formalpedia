-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin26_finite_jump_generator_lower
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T13:30:11.290197+00:00
-- url     : https://prove2.me/submissions/02ba1ef2-82d5-4e11-88f9-0f351e353659

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin26_negative_jump_generator_kernel_lower
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- Integrate the actual original generator kernel against finite negative jump intensity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y : ℝ)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (hGenerator : X.GeneratorIntegrable w y)
    (hReward : ∀ t : ℝ, t ≤ y → 0 ≤ w t)
    (hDeriv : 0 ≤ deriv w y) :
    -((X.ν (Iio (0 : ℝ))).toReal) * w y ≤
      ∫ z in Iio (0 : ℝ), SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν := by
  letI : IsFiniteMeasure (X.ν.restrict (Iio (0 : ℝ))) := ⟨by simpa using hFinite⟩
  have hConst : Integrable (fun _ : ℝ => -w y) (X.ν.restrict (Iio (0 : ℝ))) :=
    integrable_const _
  have hAE : ∀ᵐ z ∂X.ν.restrict (Iio (0 : ℝ)),
      -w y ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by
    filter_upwards [ae_restrict_mem (μ := X.ν) measurableSet_Iio] with z hz
    apply avram_mix_fin26_negative_jump_generator_kernel_lower w y z hz
    · apply hReward (y + z)
      exact add_le_of_nonpos_right (le_of_lt hz)
    · exact hDeriv
  have hBound := integral_mono_ae hConst hGenerator hAE
  simpa [integral_const, measureReal_def, smul_eq_mul, mul_neg, neg_mul] using hBound
