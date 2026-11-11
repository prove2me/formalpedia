-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger70_original_stopped_source_inactive_cell_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:28:41.088539+00:00
-- url     : https://prove2.me/submissions/834985f0-3c32-4c42-a439-faffe063f3b0

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal
noncomputable section

/-- Once the physical grid reaches its stopping horizon, the stopped source
    has no further discount or spatial increment on that cell. -/
theorem solution
    (Δ : ℝ≥0) (i : ℕ) (ρ : ℝ≥0)
    (q x : ℝ) (X D : ℝ≥0 → ℝ)
    (hinactive : ρ ≤ (i : ℝ≥0) * Δ) :
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    Real.exp (-(q * (v (i + 1) : ℝ))) =
        Real.exp (-(q * (v i : ℝ))) ∧
      x + X (v (i + 1)) - D (v i) =
        x + X (v i) - D (v i) := by
  intro v
  have hmono : (i : ℝ≥0) * Δ ≤ ((i + 1 : ℕ) : ℝ≥0) * Δ := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ i) (show (0 : ℝ≥0) ≤ Δ from bot_le)
  have hnext : ρ ≤ ((i + 1 : ℕ) : ℝ≥0) * Δ := hinactive.trans hmono
  have hv0 : v i = ρ := min_eq_right hinactive
  have hv1 : v (i + 1) = ρ := min_eq_right hnext
  simp [hv0, hv1]
