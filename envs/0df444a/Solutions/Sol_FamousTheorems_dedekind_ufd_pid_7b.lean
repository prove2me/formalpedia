-- Prove2me | solution 1 for FamousTheorems.dedekind_ufd_pid_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:59:11.915026+00:00
-- url     : https://prove2.me/submissions/51b31f9d-8d06-484e-910f-8fda39c10089

import Mathlib

theorem solution (R : Type*) [CommRing R] [IsDedekindDomain R] [UniqueFactorizationMonoid R] : IsPrincipalIdealRing R :=
  IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid R
