-- Prove2me | solution 1 for FamousTheorems.going_up
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:15:35.171953+00:00
-- url     : https://prove2.me/submissions/191501f7-dd37-4c91-b067-e8a8f7328887

import Mathlib

theorem solution {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S] (P : Ideal R) [P.IsPrime]
    (I : Ideal S) [I.IsPrime] (hIP : Ideal.comap (algebraMap R S) I ≤ P) :
    ∃ Q ≥ I, Q.IsPrime ∧ Ideal.comap (algebraMap R S) Q = P :=
  Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P I hIP
