-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB40_finitecap_smooth_gradient_restrict_interior_clip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T13:41:39.385818+00:00
-- url     : https://prove2.me/submissions/0ba469b5-b0d1-4549-bfb4-d626482ad057

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (b : ℝ) (hbc : ENNReal.ofReal b < C) :
    ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal b} ∧
    (∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal b → 1 ≤ deriv w y) := by
  have hsubset :
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal b} ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨hy.1, lt_trans hy.2 hbc⟩
  constructor
  · exact (hw_smooth.of_le (by norm_num)).mono hsubset
  · intro y hy hb
    exact hw_grad y hy (lt_trans hb hbc)
