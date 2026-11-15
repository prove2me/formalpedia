-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB45_original_finitecap_rational_clip_favourable_localtime_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:07:37.7503+00:00
-- url     : https://prove2.me/submissions/e6325588-0778-4d01-b033-efeeecfe9bf3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
import Theorems.Thm_AvramDividend_Classical_avram_gbB42_original_finitecap_interior_kink_favourable_localtime
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
    (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b ∧
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b ∧
    1 - deriv w b ≤ 0 := by
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hb :=
    avram_gbB41_original_finitecap_rational_clip_strict_interior
      C hC hFiniteCap j
  exact avram_gbB42_original_finitecap_interior_kink_favourable_localtime
    w C hw_smooth hw_grad b hb.1 hb.2
