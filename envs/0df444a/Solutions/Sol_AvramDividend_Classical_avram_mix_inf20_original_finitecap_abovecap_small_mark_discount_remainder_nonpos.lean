-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovecap_small_mark_discount_remainder_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:24:44.887546+00:00
-- url     : https://prove2.me/submissions/76bb25ab-0886-4949-9a73-4964f935975b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
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
    (δ q t y z : ℝ) (hδcap : δ ≤ C.toReal)
    (hy : C.toReal < y) (hz : -δ ≤ z) :
    let V : ℝ → ℝ := fun s =>
      if s ≤ C.toReal then w s else w C.toReal + (s - C.toReal)
    Real.exp (-(q * t)) *
      (V (y + z) - V y - deriv V y * z) ≤ 0 := by
  have hpost : 0 ≤ y + z := by linarith
  exact avram_mix_inf20_original_finitecap_discounted_nonruin_mark_HJB_signed
    C hC hFinite w hw_cont hw_smooth hw_grad
    q t y z hy hpost
