-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_additive_ENNReal_mean_integer_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:25:25.954519+00:00
-- url     : https://prove2.me/submissions/5c5ed448-cc36-4073-881e-09c522a39552

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal

/-- A zero-based additive ENNReal mean scales linearly on integer horizons. -/
theorem solution (f : ℝ≥0 → ℝ≥0∞) (hzero : f 0 = 0)
    (hadd : ∀ s t : ℝ≥0, f (s + t) = f s + f t) (n : ℕ) :
    f (n : ℝ≥0) = (n : ℝ≥0∞) * f 1 := by
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      have hsucc : f ((n + 1 : ℕ) : ℝ≥0) =
          f (n : ℝ≥0) + f 1 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hadd (n : ℝ≥0) 1
      calc
        f ((n + 1 : ℕ) : ℝ≥0) = f (n : ℝ≥0) + f 1 := hsucc
        _ = (n : ℝ≥0∞) * f 1 + f 1 := by rw [ih]
        _ = ((n + 1 : ℕ) : ℝ≥0∞) * f 1 := by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
