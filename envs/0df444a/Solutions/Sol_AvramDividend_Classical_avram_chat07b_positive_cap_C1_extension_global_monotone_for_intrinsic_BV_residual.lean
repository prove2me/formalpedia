-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat07b_positive_cap_C1_extension_global_monotone_for_intrinsic_BV_residual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:41:55.107526+00:00
-- url     : https://prove2.me/submissions/c2aa0541-59f1-46a0-91e8-c17e61bce872

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_ennreal_cap_extension_global_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_zero_extension_global_monotone_of_secant

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal)) :
    Monotone V := by
  have hVneg : ∀ y : ℝ, y < 0 → V y = 0 := by
    intro y hy
    by_cases htop : C = ⊤
    · rw [hVtop htop y]
      exact hw_neg y hy
    · rw [hVfinite htop y]
      have hyC : y ≤ C.toReal :=
        le_trans (le_of_lt hy) ENNReal.toReal_nonneg
      simp only [if_pos hyC]
      exact hw_neg y hy
  have hVzero : V 0 = w 0 := by
    by_cases htop : C = ⊤
    · exact hVtop htop 0
    · rw [hVfinite htop 0]
      exact if_pos ENNReal.toReal_nonneg
  have hV0 : 0 ≤ V 0 := by
    rw [hVzero]
    exact hw0
  have hVsec : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      b - a ≤ V b - V a := by
    intro a b ha hab
    exact avram_wave5_04b_positive_ennreal_cap_extension_global_secant
      C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite a b ha hab
  exact avram_wave6_08_zero_extension_global_monotone_of_secant
    V hVneg hV0 hVsec
