-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_ge_one_abovebarrier_full_generator_negative_marks_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:37:28.943667+00:00
-- url     : https://prove2.me/submissions/dd13d4ff-7617-4d0a-8e8a-2a3fa197c9a3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hCapOne : 1 ≤ C.toReal)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : z < 0) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
      y z ≤ 0 := by
  have hCpos : 0 < C := by
    by_contra hc
    have hzero : C = 0 := le_antisymm (le_of_not_gt hc) bot_le
    have hreal : C.toReal = 0 := by simp [hzero]
    linarith
  by_cases hsmall : -1 < z
  · have hmem : z ∈ Ioo (-1 : ℝ) 1 := ⟨hsmall, by linarith⟩
    have hpost : 0 ≤ y + z := by linarith
    have h :=
      avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
        C hCpos hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy
    have heq : max 0 (-(y + z)) = 0 :=
      max_eq_left (neg_nonpos.mpr hpost)
    have hh : SpectrallyNegativeLevy.generatorIntegrand
        (fun t => if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal))
        y z ≤ max 0 (-(y + z)) := by
      simpa [SpectrallyNegativeLevy.generatorIntegrand, hmem] using h
    rw [heq] at hh
    exact hh
  · have hnot : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hzmem
      exact hsmall hzmem.1
    have h :=
      avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
        C hCpos hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
    simpa [SpectrallyNegativeLevy.generatorIntegrand, hnot] using h
