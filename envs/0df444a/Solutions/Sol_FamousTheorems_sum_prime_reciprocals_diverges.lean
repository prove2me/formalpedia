-- Prove2me | solution 1 for FamousTheorems.sum_prime_reciprocals_diverges
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:37:01.576841+00:00
-- url     : https://prove2.me/submissions/2424fb67-152b-4824-a977-2d7a2f784938

import Mathlib

theorem solution : ¬Summable ({p : ℕ | p.Prime}.indicator fun n : ℕ => (1 : ℝ) / n) :=
  not_summable_one_div_on_primes
