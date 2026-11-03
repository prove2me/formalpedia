-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_zero_extension_global_monotone_of_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:15:36.78881+00:00
-- url     : https://prove2.me/submissions/6525b127-0046-4940-9b80-4e6fb022651f

import Mathlib

open Filter Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The corrected nonnegative zero boundary bridges the zero extension
and the positive-reserve secant across a source ruin jump. -/
theorem solution
    (V : ℝ → ℝ) (hneg : ∀ y < 0, V y = 0)
    (h0 : 0 ≤ V 0)
    (hsec : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b - a ≤ V b - V a) :
    Monotone V := by
  intro a b hab
  by_cases hbneg : b < 0
  · have haneg : a < 0 := lt_of_le_of_lt hab hbneg
    rw [hneg a haneg, hneg b hbneg]
  · have hb0 : 0 ≤ b := le_of_not_gt hbneg
    by_cases haneg : a < 0
    · have h0b : V 0 ≤ V b := by
        have h := hsec 0 b (le_refl 0) hb0
        linarith
      rw [hneg a haneg]
      linarith
    · have ha0 : 0 ≤ a := le_of_not_gt haneg
      have h := hsec a b ha0 hab
      linarith
