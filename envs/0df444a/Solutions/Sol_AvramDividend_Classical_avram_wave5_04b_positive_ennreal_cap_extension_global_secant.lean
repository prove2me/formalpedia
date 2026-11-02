-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_positive_ennreal_cap_extension_global_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:31:08.437289+00:00
-- url     : https://prove2.me/submissions/b0c2589d-b7e3-44e0-b1fb-d75f92b0facd

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The positive ENNReal cap admits a globally source-safe value extension: cap-linear when finite and w itself at infinity. Its secant controls every nonnegative reserve decrement without strict interior hypotheses. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ V b - V a := by
  by_cases htop : C = ⊤
  · have hSec := avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad a b ha hab (by simp [htop])
    rw [hVtop htop a, hVtop htop b]
    exact hSec
  · have hc : 0 < C.toReal :=
      ENNReal.toReal_pos_iff.mpr ⟨hC, lt_top_iff_ne_top.mpr htop⟩
    have hcap : ENNReal.ofReal C.toReal = C :=
      ENNReal.ofReal_toReal htop
    have hsmoothFinite :
        ContDiffOn ℝ 1 w
          {z : ℝ | 0 < z ∧
            ENNReal.ofReal z < ENNReal.ofReal C.toReal} := by
      simpa [hcap] using hw_smooth
    have hgradFinite : ∀ z : ℝ, 0 < z →
        ENNReal.ofReal z < ENNReal.ofReal C.toReal →
          1 ≤ deriv w z := by
      intro z hz hzc
      exact hw_grad z hz (by simpa [hcap] using hzc)
    have hSec := avram_wave4_04_cap_linear_extension_full_secant
      C.toReal hc w hw_cont hsmoothFinite hgradFinite a b ha hab
    rw [hVfinite htop b, hVfinite htop a]
    exact hSec
