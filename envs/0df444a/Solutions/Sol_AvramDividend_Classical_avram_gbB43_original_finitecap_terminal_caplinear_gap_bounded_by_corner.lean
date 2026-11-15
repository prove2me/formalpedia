-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB43_original_finitecap_terminal_caplinear_gap_bounded_by_corner
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:56:47.672021+00:00
-- url     : https://prove2.me/submissions/132d7736-5efd-4fc8-ae13-d2ece91e6926

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b y : ℝ) (hb0 : 0 ≤ b) (hbC : b ≤ C.toReal)
    (hy0 : 0 ≤ y) (hyC : y ≤ C.toReal)
    (hyCap : ENNReal.ofReal y ≤ C) :
    let V : ℝ → ℝ := fun z =>
      if z ≤ b then w z else w b + (z - b)
    0 ≤ w y - V y ∧
      w y - V y ≤ (w C.toReal - w b) - (C.toReal - b) := by
  let V : ℝ → ℝ := fun z =>
    if z ≤ b then w z else w b + (z - b)
  have hcap : ENNReal.ofReal C.toReal ≤ C := by
    simpa using le_of_eq (ENNReal.ofReal_toReal hFiniteCap)
  have hsBC :=
    avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
      C w hw_cont hw_smooth hw_grad b C.toReal hb0 hbC hcap
  change 0 ≤ w y - V y ∧
    w y - V y ≤ (w C.toReal - w b) - (C.toReal - b)
  by_cases hyb : y ≤ b
  · have hv : V y = w y := by simp [V, hyb]
    rw [hv]
    constructor <;> linarith
  · have hby : b ≤ y := le_of_lt (lt_of_not_ge hyb)
    have hsBY :=
      avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
        C w hw_cont hw_smooth hw_grad b y hb0 hby hyCap
    have hsYC :=
      avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
        C w hw_cont hw_smooth hw_grad y C.toReal hy0 hyC hcap
    have hv : V y = w b + (y - b) := by
      simp [V, not_le.mpr (lt_of_not_ge hyb)]
    rw [hv]
    constructor <;> linarith
