-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_ruin_overshoot_caplinear_mark_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:26:17.869389+00:00
-- url     : https://prove2.me/submissions/0cf89991-6af8-4fab-8d78-02ec3454025b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
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
    (y z : ℝ) (hy : C.toReal < y) (hz : y + z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    V (y + z) - V y - deriv V y * z ≤ -(y + z) := by
  dsimp only
  have hc0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
  have hCcap : ENNReal.ofReal C.toReal ≤ C := by
    simpa [ENNReal.ofReal_toReal hFinite]
  have hsec :=
    avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad
      0 C.toReal (by norm_num) hc0 hCcap
  have hcap : C.toReal ≤ w C.toReal := by
    linarith
  have hd :
      deriv (fun t : ℝ =>
        if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)) y = 1 :=
    (avram_gbB31_interior_caplinear_affine_upper_derivatives
      w C.toReal y hy).1
  have hle : y + z ≤ C.toReal := le_trans (le_of_lt hz) hc0
  rw [if_pos hle, hw_neg (y + z) hz,
      if_neg (not_le.mpr hy), hd]
  linarith
