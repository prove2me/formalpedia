-- Prove2me | solution 1 for FamousTheorems.multinomial_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:19:02.980846+00:00
-- url     : https://prove2.me/submissions/16ce49d9-589d-4802-aad8-f4c3a6f440e1

import Mathlib

theorem solution {α R : Type*} [DecidableEq α] [CommSemiring R] (s : Finset α) (f : α → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ n = ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : R) * ∏ i ∈ s, f i ^ k i :=
  Finset.sum_pow_eq_sum_piAntidiag s f n
