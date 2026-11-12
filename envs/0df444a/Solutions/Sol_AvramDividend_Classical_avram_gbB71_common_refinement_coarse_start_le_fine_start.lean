-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB71_common_refinement_coarse_start_le_fine_start
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T16:07:47.474062+00:00
-- url     : https://prove2.me/submissions/72b37a30-f3d6-4590-a53f-1baecc4bcf38

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution (r m p : ℕ) (n : ℝ≥0) :
    (((r / (p + 1) : ℕ) : ℝ≥0) *
      (n / ((m + 1 : ℕ) : ℝ≥0))) ≤
      (r : ℝ≥0) *
        (n / (((m + 1) * (p + 1) : ℕ) : ℝ≥0)) := by
  have hm : (0 : ℝ≥0) < ((m + 1 : ℕ) : ℝ≥0) := by positivity
  have hp : (0 : ℝ≥0) < ((p + 1 : ℕ) : ℝ≥0) := by positivity
  have hbound :
      ((r / (p + 1) : ℕ) : ℝ≥0) * ((p + 1 : ℕ) : ℝ≥0) ≤ r := by
    exact_mod_cast Nat.div_mul_le_self r (p + 1)
  have hden : (n / (((m + 1) * (p + 1) : ℕ) : ℝ≥0)) =
      (n / ((m + 1 : ℕ) : ℝ≥0)) / ((p + 1 : ℕ) : ℝ≥0) := by
    apply Subtype.ext
    simp only [NNReal.coe_div, NNReal.coe_mul, Nat.cast_mul]
    field_simp [show (((m + 1 : ℕ) : ℝ)) ≠ 0 by positivity,
      show (((p + 1 : ℕ) : ℝ)) ≠ 0 by positivity]
  rw [hden]
  calc
    (((r / (p + 1) : ℕ) : ℝ≥0) *
        (n / ((m + 1 : ℕ) : ℝ≥0))) =
        (((r / (p + 1) : ℕ) : ℝ≥0) * ((p + 1 : ℕ) : ℝ≥0)) *
          ((n / ((m + 1 : ℕ) : ℝ≥0)) / ((p + 1 : ℕ) : ℝ≥0)) := by
            field_simp [ne_of_gt hp]
    _ ≤ (r : ℝ≥0) *
        ((n / ((m + 1 : ℕ) : ℝ≥0)) / ((p + 1 : ℕ) : ℝ≥0)) := by
          exact mul_le_mul_of_nonneg_right hbound (by positivity)
