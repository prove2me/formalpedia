-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_ennreal_drift_budget_strict_horizon_to_closed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:40:46.444751+00:00
-- url     : https://prove2.me/submissions/bc928f16-ba8a-473c-8eeb-67965e3d2541

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- A nonnegative drift allowance valid at every strictly later finite
    horizon also bounds its endpoint allowance, including infinite rewards. -/
theorem solution
    (a d T : ℝ≥0) (u : ℝ≥0∞)
    (h : ∀ H : ℝ≥0, T < H →
      u ≤ ((a + H * d : ℝ≥0) : ℝ≥0∞)) :
    u ≤ ((a + T * d : ℝ≥0) : ℝ≥0∞) := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : ℝ≥0 := ε / (d + 1)
  have hdpos : 0 < d + 1 := by positivity
  have hδpos : 0 < δ := div_pos hε hdpos
  have hmul : δ * d ≤ ε := by
    have hden : d ≤ d + 1 :=
      le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ 1 from zero_le)
    have hcancel : δ * (d + 1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ ε (ne_of_gt hdpos)
    exact (mul_le_mul_of_nonneg_left hden
      (show (0 : ℝ≥0) ≤ δ from zero_le)).trans_eq hcancel
  have hH : T < T + δ := lt_add_of_pos_right T hδpos
  calc
    u ≤ ((a + (T + δ) * d : ℝ≥0) : ℝ≥0∞) := h (T + δ) hH
    _ = ((a + T * d : ℝ≥0) : ℝ≥0∞) + (δ * d : ℝ≥0∞) := by
      congr 1
      norm_cast
      ring
    _ ≤ ((a + T * d : ℝ≥0) : ℝ≥0∞) + (ε : ℝ≥0∞) := by
      exact add_le_add le_rfl (by exact_mod_cast hmul)
