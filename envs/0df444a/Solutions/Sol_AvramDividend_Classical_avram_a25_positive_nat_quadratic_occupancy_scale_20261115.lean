-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_positive_nat_quadratic_occupancy_scale_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:57:06.5971+00:00
-- url     : https://prove2.me/submissions/c3a7f367-4faf-4a2f-983a-26cb47f81711

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Positive natural grid spacing rescales quadratic void-count bounds. -/
theorem solution
    (n : ℕ) (hn : 0 < n) (r q : ℝ)
    (h : r / (n : ℝ) - (r / (n : ℝ)) ^ 2 / 2 ≤ q ∧
      q ≤ r / (n : ℝ)) :
    r - (r ^ 2 / 2) * (1 / (n : ℝ)) ≤ (n : ℝ) * q ∧
      (n : ℝ) * q ≤ r := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnNe : (n : ℝ) ≠ 0 := ne_of_gt hnR
  constructor
  · have hm := mul_le_mul_of_nonneg_left h.1 (le_of_lt hnR)
    have he : (n : ℝ) * (r / (n : ℝ) -
        (r / (n : ℝ)) ^ 2 / 2) =
        r - (r ^ 2 / 2) * (1 / (n : ℝ)) := by
      field_simp [hnNe]
    simpa only [he] using hm
  · have hm := mul_le_mul_of_nonneg_left h.2 (le_of_lt hnR)
    have he : (n : ℝ) * (r / (n : ℝ)) = r := by
      field_simp [hnNe]
    simpa only [he] using hm
