-- Prove2me | solution 1 for FamousTheorems.fibonacci_shallow_diagonal_binomial_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:16:54.75811+00:00
-- url     : https://prove2.me/submissions/d03f1ffc-4c53-4be9-97dd-8cd444615e58

import Mathlib

theorem solution (n : ℕ) : Nat.fib (n + 1) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, p.1.choose p.2 :=
  Nat.fib_succ_eq_sum_choose n
