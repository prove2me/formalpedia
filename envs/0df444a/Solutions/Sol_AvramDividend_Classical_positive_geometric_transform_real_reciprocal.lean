-- Prove2me | solution 1 for AvramDividend.Classical.positive_geometric_transform_real_reciprocal
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T07:21:37.878048+00:00
-- url     : https://prove2.me/submissions/5d60696c-9598-45a3-8c58-20e28e0418d9

import Mathlib
set_option autoImplicit false
open scoped ENNReal

theorem solution
    (δ s J : ℝ) (hδ : 0 < δ) (hs : 0 < s)
    (hJ : 0 ≤ J) (hgap : J < δ * s) :
    ENNReal.ofReal (1 / s) *
        ((ENNReal.ofReal δ)⁻¹ *
          (1 - (ENNReal.ofReal δ)⁻¹ * ENNReal.ofReal (J / s))⁻¹) =
      ENNReal.ofReal ((δ * s - J)⁻¹) := by
  have hx0 : 0 ≤ δ⁻¹ * (J / s) := by positivity
  have hx1 : δ⁻¹ * (J / s) < 1 := by
    have : δ⁻¹ * (J / s) = J / (δ * s) := by field_simp
    rw [this, div_lt_one (by positivity)]; exact hgap
  have hpos : 0 < 1 - δ⁻¹ * (J / s) := by linarith
  have h1 : (ENNReal.ofReal δ)⁻¹ = ENNReal.ofReal δ⁻¹ := (ENNReal.ofReal_inv_of_pos hδ).symm
  have h2 : (1 : ℝ≥0∞) - ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (J / s)
      = ENNReal.ofReal (1 - δ⁻¹ * (J / s)) := by
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one]
  rw [h1, h2, ← ENNReal.ofReal_inv_of_pos hpos, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hne : δ * s - J ≠ 0 := by linarith
  have hδ0 : δ ≠ 0 := hδ.ne'
  have hs0 : s ≠ 0 := hs.ne'
  have : 1 - δ⁻¹ * (J / s) = (δ * s - J) / (δ * s) := by field_simp
  rw [this]
  field_simp
