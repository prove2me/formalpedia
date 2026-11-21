-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_largebarrier_full_generator_HJB_from_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:09:08.658148+00:00
-- url     : https://prove2.me/submissions/bb3afd2f-d4e9-456a-b4a4-685bb55a7a24

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_ge_one_abovebarrier_full_generator_negative_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hCapOne : 1 ≤ C.toReal)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q y : ℝ) (hy : C.toReal < y)
    (hGI : Integrable (fun z : ℝ =>
      SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z) (X.ν.restrict (Iio (0 : ℝ))))
    (hDrift : X.c ≤ q * (w C.toReal + (y - C.toReal))) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    X.generator V y - q * V y ≤ 0 := by
  dsimp only
  have hJump : (∫ z in Iio (0 : ℝ),
      SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z ∂X.ν) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iio] with z hz
    exact avram_mix_inf20_original_finitecap_ge_one_abovebarrier_full_generator_negative_marks_nonpos
      C hFinite hCapOne w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
  rw [avram_mix_inf20_original_above_finitecap_full_generator_reduces_to_drift_jump
    X w C.toReal y hy]
  rw [if_neg (not_le.mpr hy)]
  linarith
