-- Prove2me | solution 1 for AvramDividend.Classical.causal_quadratic_pointwise_bound_uniform_above_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T22:07:04.787291+00:00
-- url     : https://prove2.me/submissions/bbdc3065-c45d-4a14-bcec-2d5e4413aee5

import Mathlib.Analysis.Convolution
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A pointwise quadratic-geometric upper bound becomes uniform on each
positive half-line away from the origin. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) :
    ∀ δ : ℝ, 0 < δ → ∀ n : ℕ, ∀ x : ℝ, δ ≤ x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / δ := by
  intro δ hδ n x hx
  have hcoeff : 0 ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) :=
    mul_nonneg (sq_nonneg _) (pow_nonneg hρ _)
  exact (hpoint n x (lt_of_lt_of_le hδ hx)).trans
    (div_le_div_of_nonneg_left hcoeff hδ hx)
