-- Prove2me | solution 1 for FamousTheorems.sum_of_two_squares_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:15:05.307289+00:00
-- url     : https://prove2.me/submissions/7ad0a078-cc0a-4a53-a8c0-3e98a2472666

import Mathlib

theorem solution {n : ℕ} : (∃ x y : ℕ, n = x ^ 2 + y ^ 2) ↔ ∀ q ∈ n.primeFactors, q % 4 = 3 → Even (padicValNat q n) :=
  Nat.eq_sq_add_sq_iff
