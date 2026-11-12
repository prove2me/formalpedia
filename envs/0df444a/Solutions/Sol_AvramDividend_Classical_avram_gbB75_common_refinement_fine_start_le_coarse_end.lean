-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB75_common_refinement_fine_start_le_coarse_end
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:43:17.730712+00:00
-- url     : https://prove2.me/submissions/a9952820-376e-4f3f-8ecd-ba7076b7efb7

import Mathlib
open scoped NNReal
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution (r m p : ℕ) (n : ℝ≥0) :
    (r : ℝ≥0) *
      (n / (((m + 1) * (p + 1) : ℕ) : ℝ≥0)) ≤
      (((r / (p + 1) + 1 : ℕ) : ℝ≥0) *
        (n / ((m + 1 : ℕ) : ℝ≥0))) := by
  have hnat : r ≤ (r / (p + 1) + 1) * (p + 1) := by
    have hm := Nat.mod_lt r (by omega : 0 < p + 1)
    have hd := Nat.mod_add_div r (p + 1)
    nlinarith
  have hbound : (r : ℝ≥0) ≤
      (((r / (p + 1) + 1 : ℕ) : ℝ≥0) *
        ((p + 1 : ℕ) : ℝ≥0)) := by exact_mod_cast hnat
  have hp : (0 : ℝ≥0) < ((p + 1 : ℕ) : ℝ≥0) := by positivity
  have hden : (n / (((m + 1) * (p + 1) : ℕ) : ℝ≥0)) =
      (n / ((m + 1 : ℕ) : ℝ≥0)) /
        ((p + 1 : ℕ) : ℝ≥0) := by
    apply Subtype.ext
    simp only [NNReal.coe_div, NNReal.coe_mul, Nat.cast_mul]
    field_simp [show (((m + 1 : ℕ) : ℝ)) ≠ 0 by positivity,
      show (((p + 1 : ℕ) : ℝ)) ≠ 0 by positivity]
  rw [hden]
  calc
    (r : ℝ≥0) *
        ((n / ((m + 1 : ℕ) : ℝ≥0)) /
          ((p + 1 : ℕ) : ℝ≥0)) ≤
        (((r / (p + 1) + 1 : ℕ) : ℝ≥0) *
          ((p + 1 : ℕ) : ℝ≥0)) *
          ((n / ((m + 1 : ℕ) : ℝ≥0)) /
            ((p + 1 : ℕ) : ℝ≥0)) := by
            exact mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (((r / (p + 1) + 1 : ℕ) : ℝ≥0) *
        (n / ((m + 1 : ℕ) : ℝ≥0))) := by
          field_simp [ne_of_gt hp]
