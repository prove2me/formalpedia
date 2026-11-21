-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_actual_truncated_generator_mark_overshoot
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:30:50.586782+00:00
-- url     : https://prove2.me/submissions/edfe012e-f3d2-4686-bde0-8cfcafd34df7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
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
    (y z : ℝ) (hy : C.toReal < y) (hz : z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    SpectrallyNegativeLevy.generatorIntegrand V y z ≤
      if -1 < z then max 0 (-(y + z)) else 0 := by
  dsimp only
  by_cases hsmall : -1 < z
  · have hmem : z ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    have h :=
      avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy
    simpa [SpectrallyNegativeLevy.generatorIntegrand, hmem, hsmall] using h
  · have hnot : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hzmem
      exact hsmall hzmem.1
    have h :=
      avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
    simpa [SpectrallyNegativeLevy.generatorIntegrand, hnot, hsmall] using h
