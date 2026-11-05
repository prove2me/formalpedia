-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_factorial_of_finite_blocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:37:15.185194+00:00
-- url     : https://prove2.me/submissions/3c2f11e2-4003-4ac4-a271-facbf92d2711

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

/-- Original finite-block factorial combinatorics with chronological strict pairs. -/
theorem solution (a : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, a i) *
        ((∑ i ∈ Finset.range n, a i) - 1) =
      (∑ i ∈ Finset.range n, a i * (a i - 1)) +
        2 * (∑ j ∈ Finset.range n,
          (∑ i ∈ Finset.range j, a i) * a j) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [Finset.sum_range_succ]
    nlinarith [ih]
