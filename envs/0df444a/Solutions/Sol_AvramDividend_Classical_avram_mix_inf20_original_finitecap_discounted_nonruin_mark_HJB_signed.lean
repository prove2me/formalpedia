-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:32:03.886299+00:00
-- url     : https://prove2.me/submissions/834ab857-f994-4dff-9edf-9d22deccfb35

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (q t y z : ℝ) (hy : C.toReal < y) (hz : 0 ≤ y + z) :
    let V : ℝ → ℝ := fun s =>
      if s ≤ C.toReal then w s else w C.toReal + (s - C.toReal)
    Real.exp (-(q * t)) *
      (V (y + z) - V y - deriv V y * z) ≤ 0 := by
  dsimp only
  have h :=
    avram_mix_inf20_original_finitecap_active_postmark_upper_strip_compensator_nonpos
      C hC hFinite w hw_cont hw_smooth hw_grad y z hy hz
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) h
