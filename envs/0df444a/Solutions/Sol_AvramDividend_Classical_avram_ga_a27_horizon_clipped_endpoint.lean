-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a27_horizon_clipped_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:36:12.37044+00:00
-- url     : https://prove2.me/submissions/b766e3c4-db7b-4dc4-a1be-59e07cedc98e

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Positivity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal
noncomputable section

theorem solution (n : ℝ≥0) (m : ℕ) (ρ : ℝ≥0) (hnρ : n ≤ ρ) :
    min (((m + 1 : ℕ) : ℝ≥0) *
      (n / ((m : ℝ≥0) + 1))) ρ = n := by
  have hcast : (((m + 1 : ℕ) : ℝ≥0)) = (m : ℝ≥0) + 1 := by norm_cast
  rw [hcast]
  have hden : (m : ℝ≥0) + 1 ≠ 0 := by positivity
  have hgrid : ((m : ℝ≥0) + 1) * (n / ((m : ℝ≥0) + 1)) = n := by
    field_simp
  rw [hgrid]
  exact min_eq_left hnρ
