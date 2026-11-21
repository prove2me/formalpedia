-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:42:41.18718+00:00
-- url     : https://prove2.me/submissions/fe42526a-d9ab-48ad-80b2-5a9576638fb0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
import Theorems.Thm_AvramDividend_Classical_avram_gbB31_interior_caplinear_affine_upper_derivatives
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
    V (y + z) - V y ≤ 0 := by
  dsimp only
  by_cases hp : 0 ≤ y + z
  · have h :=
      avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
        C hC hFinite w hw_cont hw_smooth hw_grad y z hy hp
    have hd :
        deriv (fun t : ℝ =>
          if t ≤ C.toReal then w t
          else w C.toReal + (t - C.toReal)) y = 1 :=
      (avram_gbB31_interior_caplinear_affine_upper_derivatives
        w C.toReal y hy).1
    dsimp only at h
    rw [hd] at h
    linarith
  · have hn : y + z < 0 := lt_of_not_ge hp
    have h :=
      avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
        C hC hFinite w hw0 hw_cont hw_neg hw_smooth hw_grad y z hy hn
    have hypos : 0 < y := lt_of_le_of_lt ENNReal.toReal_nonneg hy
    have hd :
        deriv (fun t : ℝ =>
          if t ≤ C.toReal then w t
          else w C.toReal + (t - C.toReal)) y = 1 :=
      (avram_gbB31_interior_caplinear_affine_upper_derivatives
        w C.toReal y hy).1
    dsimp only at h
    rw [hd] at h
    linarith
