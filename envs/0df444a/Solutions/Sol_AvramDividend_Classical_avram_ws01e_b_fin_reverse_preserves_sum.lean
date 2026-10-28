-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_b_fin_reverse_preserves_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T08:00:03.384874+00:00
-- url     : https://prove2.me/submissions/08065d51-485d-4c9e-becb-068017284697

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset
open scoped BigOperators

/-- Reversing all n finite coordinates does not change their total. -/
theorem solution (n : ℕ) (v : Fin n → ℝ) :
    (∑ i : Fin n, v i.rev) = ∑ i : Fin n, v i := by
  simpa [Fin.revPerm_apply] using
    (Equiv.Perm.sum_comp (Fin.revPerm : Equiv.Perm (Fin n)) Finset.univ v
      (by simp))
