-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_infinite_cap_gradient_global_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:29:21.945411+00:00
-- url     : https://prove2.me/submissions/4d8132d1-3ac4-45d8-b602-8a45513fcce5

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The full-cap secant inequality at cap infinity, including contact with reserve zero, without ever differentiating at zero. -/
theorem solution
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z})
    (hw_grad : ∀ z : ℝ, 0 < z → 1 ≤ deriv w z)
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    b - a ≤ w b - w a := by
  have hsmoothCap :
      ContDiffOn ℝ 1 w
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < (⊤ : ℝ≥0∞)} := by
    simpa using hw_smooth
  have hgradCap : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < (⊤ : ℝ≥0∞) → 1 ≤ deriv w z := by
    intro z hz _
    exact hw_grad z hz
  exact avram_wave3_03_bv_full_cap_gradient_secant
    (⊤ : ℝ≥0∞) (by simp) w hw_cont hsmoothCap hgradCap
    a b ha hab (by simp)
