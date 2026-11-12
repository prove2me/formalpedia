-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger89_clipped_uniform_grid_monotone_and_exhausts_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T10:10:37.604115+00:00
-- url     : https://prove2.me/submissions/82268135-81b7-44de-911c-163fc06b4110

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal
noncomputable section

theorem solution
    (n m : ℕ) (ρ : ℝ≥0) (hρ : ρ ≤ (n : ℝ≥0)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    Monotone v ∧ v 0 = 0 ∧ v (m + 2) = ρ := by
  intro Δ v
  have hden : (m : ℝ≥0) + 2 ≠ 0 := by positivity
  have hscale : ((m : ℝ≥0) + 2) * Δ = (n : ℝ≥0) := by
    dsimp [Δ]
    rw [mul_div_cancel₀]
    exact hden
  constructor
  · intro i k hik
    dsimp [v]
    apply min_le_min_right
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hik) (by positivity)
  constructor
  · simp [v]
  · change min (((m + 2 : ℕ) : ℝ≥0) * Δ) ρ = ρ
    have hcast : ((m + 2 : ℕ) : ℝ≥0) = (m : ℝ≥0) + 2 := by
      push_cast
      ring
    rw [hcast, hscale]
    exact min_eq_right hρ
