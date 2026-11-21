-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_actual_finitecap_far_upper_generatorIntegrand_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:32:56.309175+00:00
-- url     : https://prove2.me/submissions/bf8803a0-63f0-431c-952d-1419872c450f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal + 1 ≤ y) (hz : z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    SpectrallyNegativeLevy.generatorIntegrand V y z ≤ 0 := by
  dsimp only
  have hybase : C.toReal < y := by linarith
  have hs := avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
    (fun t : ℝ => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)) y
  by_cases hsmall : -1 < z
  · have hpost : C.toReal < y + z := by linarith
    rw [hs.1 z hsmall hz]
    exact le_of_eq
      (avram_mix_inf20_original_caplinear_upperband_mark_compensator_zero
        w C.toReal y z hybase hpost)
  · rw [hs.2 z (le_of_not_gt hsmall)]
    exact avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
      C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hybase hz
