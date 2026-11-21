-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T20:13:15.465862+00:00
-- url     : https://prove2.me/submissions/f9b5545a-5565-4737-8ac7-b6d66f90838c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
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
    V (y + z) - V y -
      deriv V y * (if -1 < z then z else 0) ≤ max 0 (-(y + z)) := by
  dsimp only
  by_cases hsmall : -1 < z
  · simp only [if_pos hsmall]
    exact avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
      C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy
  · have hraw :=
      avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hz
    simp only [if_neg hsmall, mul_zero, sub_zero]
    exact le_trans hraw (le_max_left 0 (-(y + z)))
