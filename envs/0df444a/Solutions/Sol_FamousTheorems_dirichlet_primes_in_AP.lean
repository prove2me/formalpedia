-- Prove2me | solution 1 for FamousTheorems.dirichlet_primes_in_AP
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:48.068974+00:00
-- url     : https://prove2.me/submissions/8225d531-d12f-4655-861e-c30306bb769e

import Mathlib

theorem solution : ∀ {q : ℕ} [NeZero q] {a : ZMod q}, IsUnit a →
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite :=
  Nat.infinite_setOfPred_prime_and_eq_mod
