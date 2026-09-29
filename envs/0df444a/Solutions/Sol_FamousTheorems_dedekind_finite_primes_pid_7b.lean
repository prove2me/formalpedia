-- Prove2me | solution 1 for FamousTheorems.dedekind_finite_primes_pid_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:58:26.021725+00:00
-- url     : https://prove2.me/submissions/b355b5b3-884f-449d-8819-6a882f2fa97a

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsDedekindDomain R] (h : {I : Ideal R | I.IsPrime}.Finite) :
    IsPrincipalIdealRing R :=
  IsPrincipalIdealRing.of_finite_primes h
