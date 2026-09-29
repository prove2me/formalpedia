-- Prove2me | solution 1 for FamousTheorems.gauss_totient_sum
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:12:58.23964+00:00
-- url     : https://prove2.me/submissions/732674b7-a6e1-47a7-9d3a-2b1a25a26811

import Mathlib

theorem solution (n : ℕ) : ∑ d ∈ n.divisors, Nat.totient d = n :=
  Nat.sum_totient n
