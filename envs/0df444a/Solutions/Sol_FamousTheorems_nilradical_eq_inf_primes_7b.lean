-- Prove2me | solution 1 for FamousTheorems.nilradical_eq_inf_primes_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:56:55.41011+00:00
-- url     : https://prove2.me/submissions/91b0039e-550b-40f1-8efc-4311eddc6ff0

import Mathlib

theorem solution (R : Type*) [CommSemiring R] : nilradical R = sInf {J : Ideal R | J.IsPrime} :=
  nilradical_eq_sInf R
