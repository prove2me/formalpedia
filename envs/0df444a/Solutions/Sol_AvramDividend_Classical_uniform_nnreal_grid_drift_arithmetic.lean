-- Prove2me | solution 1 for AvramDividend.Classical.uniform_nnreal_grid_drift_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T15:01:10.364449+00:00
-- url     : https://prove2.me/submissions/3238ebac-56ec-43d8-898e-6c978d046912

import Mathlib.Data.NNReal.Defs
import Mathlib.Tactic.Ring
open scoped NNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Equal NNReal grid steps have equal real drift increments, and their
rescaled drift threshold agrees with the full-horizon drift. -/
theorem solution
    (d : ℝ) (T δ : ℝ≥0) (N : ℕ) (ts : ℕ → ℝ≥0)
    (hStep : ∀ k : ℕ, k < N → ts k ≤ ts (k + 1))
    (hSpacing : ∀ k : ℕ, k < N → ts (k + 1) - ts k = δ)
    (hLength : (N : ℝ≥0) * δ = T) :
    (∀ k : ℕ, k < N →
      d * ((ts (k + 1) : ℝ) - (ts k : ℝ)) = d * (δ : ℝ)) ∧
    (N : ℝ) * (d * (δ : ℝ)) = d * (T : ℝ) := by
  constructor
  · intro k hk
    calc
      d * ((ts (k + 1) : ℝ) - (ts k : ℝ)) =
          d * ((ts (k + 1) - ts k : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sub (hStep k hk)]
      _ = d * (δ : ℝ) := by rw [hSpacing k hk]
  · have hCast : (N : ℝ) * (δ : ℝ) = (T : ℝ) := by
      exact_mod_cast hLength
    calc
      (N : ℝ) * (d * (δ : ℝ)) =
          d * ((N : ℝ) * (δ : ℝ)) := by ring
      _ = d * (T : ℝ) := by rw [hCast]
