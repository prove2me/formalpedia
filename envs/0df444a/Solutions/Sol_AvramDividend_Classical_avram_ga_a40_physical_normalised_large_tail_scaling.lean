-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a40_physical_normalised_large_tail_scaling
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:37:25.189237+00:00
-- url     : https://prove2.me/submissions/97121dce-71a9-45bf-b77a-be3559ad117b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp

-- Undo normalisation by the positive original Gaussian volatility on large increments.
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (z σ η : ℝ) (hσ : 0 < σ) (hη : 0 < η) :
    (if η ≤ |z| then z ^ 2 else 0) =
      σ ^ 2 * (if η / σ ≤ |z / σ| then (z / σ) ^ 2 else 0) := by
  have hiff : η ≤ |z| ↔ η / σ ≤ |z / σ| := by
    simpa only [abs_div, abs_of_pos hσ] using
      (div_le_div_iff_of_pos_right hσ).symm
  by_cases h : η ≤ |z|
  · have hnorm : η / σ ≤ |z / σ| := hiff.mp h
    simp only [if_pos h, if_pos hnorm]
    have hs : σ ≠ 0 := ne_of_gt hσ
    field_simp
  · have hnorm : ¬ η / σ ≤ |z / σ| := by
      intro hn
      exact h (hiff.mpr hn)
    simp only [if_neg h, if_neg hnorm, mul_zero]
