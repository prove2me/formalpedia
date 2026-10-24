-- Prove2me | solution 1 for AvramDividend.Classical.causal_ramp_remainder_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:36:05.576597+00:00
-- url     : https://prove2.me/submissions/6d4a0797-ca97-4f39-aa37-49019b8666aa

import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- After removing the ramp-scaled kernel, only the small positive-time part remains. -/
theorem solution
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hfzero : ∀ x : ℝ, x ≤ 0 → f x = 0) :
    (∀ x : ℝ, x ≤ 0 →
      f x - max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x = 0) ∧
    (∀ x : ℝ, 2 * ε ≤ x →
      f x - max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x = 0) := by
  obtain ⟨_, _, hχone⟩ :=
    positive_ramp_cutoff_continuous_and_support ε hε
  constructor
  · intro x hx
    rw [hfzero x hx]
    ring
  · intro x hx
    rw [hχone x hx]
    ring
