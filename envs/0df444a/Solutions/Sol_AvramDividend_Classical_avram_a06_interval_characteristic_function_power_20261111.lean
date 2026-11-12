-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_interval_characteristic_function_power_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:23:14.580539+00:00
-- url     : https://prove2.me/submissions/63937acd-9767-42ae-8a80-f4793c056dc4

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- A concatenation law and common unit increment imply a power law. -/
theorem solution
    (F : ℕ → ℕ → ℂ) (z : ℂ)
    (hEmpty : ∀ a, F a a = 1)
    (hUnit : ∀ a, F a (a + 1) = z)
    (hConcat : ∀ a b c, a ≤ b → b ≤ c → F a c = F a b * F b c)
    (a k : ℕ) : F a (a + k) = z ^ k := by
  induction k with
  | zero => simpa using hEmpty a
  | succ k ih =>
      calc
        F a (a + (k + 1)) = F a (a + k) * F (a + k) ((a + k) + 1) := by
          rw [Nat.add_succ]
          exact hConcat a (a + k) ((a + k) + 1) (by omega) (by omega)
        _ = z ^ k * z := by rw [ih, hUnit (a + k)]
        _ = z ^ (k + 1) := (pow_succ z k).symm
