-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB47_original_finitecap_discounted_kink_localtime_correction_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:16:27.388052+00:00
-- url     : https://prove2.me/submissions/4f9e2c37-b4c8-4902-aad0-10602574648d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) (L E : ℝ) (hL : 0 ≤ L) (hE : 0 ≤ E) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    E * (((1 - deriv w b) / 2) * L) ≤ 0 := by
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  change E * (((1 - deriv w b) / 2) * L) ≤ 0
  have hKink :=
    (avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
      w C hC hFiniteCap hw_smooth hw_grad j).2.2
  have hSlope : (1 - deriv w b) / 2 ≤ 0 := by
    linarith
  exact mul_nonpos_of_nonneg_of_nonpos hE
    (mul_nonpos_of_nonpos_of_nonneg hSlope hL)
