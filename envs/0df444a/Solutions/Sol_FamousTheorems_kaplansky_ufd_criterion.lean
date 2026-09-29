-- Prove2me | solution 1 for FamousTheorems.kaplansky_ufd_criterion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:27.195547+00:00
-- url     : https://prove2.me/submissions/37ea0365-9de5-418a-bd01-d10f39e3df88

import Mathlib

theorem solution {R : Type*} [CommSemiring R] [IsDomain R] :
    UniqueFactorizationMonoid R ↔ ∀ I ≠ (⊥ : Ideal R), I.IsPrime → ∃ x ∈ I, Prime x :=
  UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime
