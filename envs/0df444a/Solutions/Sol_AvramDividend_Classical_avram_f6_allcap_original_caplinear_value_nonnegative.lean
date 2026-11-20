-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_allcap_original_caplinear_value_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:30:28.753667+00:00
-- url     : https://prove2.me/submissions/6c8b0ee6-4082-44af-87e9-27eb39f61c1f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_f6_caplinear_ofReal_real_switch_exact
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (z : ℝ) (hz : 0 ≤ z) :
    0 ≤ (if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) := by
  let V : ℝ → ℝ := fun y =>
    if ENNReal.ofReal y ≤ C then w y
    else w C.toReal + (y - C.toReal)
  have hVtop : C = ⊤ → ∀ y : ℝ, V y = w y := by
    intro h y
    simp [V, h]
  have hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal) := by
    intro h y
    have hEq :=
      avram_f6_caplinear_ofReal_real_switch_exact C hC w y
    simpa [V, h] using hEq
  have hSec :=
    avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad
      hVtop hVfinite 0 z (le_refl 0) hz
  have hVzero : V 0 = w 0 := by
    simp [V, le_of_lt hC]
  change 0 ≤ V z
  rw [hVzero] at hSec
  linarith
