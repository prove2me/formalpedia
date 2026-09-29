-- Prove2me | solution 1 for FamousTheorems.vandermonde_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:07:09.499993+00:00
-- url     : https://prove2.me/submissions/91957fc8-8f15-4fb7-9f60-b4b231470bf4

import Mathlib

theorem solution (m n k : ℕ) :
    (m + n).choose k = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal k, m.choose ij.1 * n.choose ij.2 :=
  Nat.add_choose_eq m n k
