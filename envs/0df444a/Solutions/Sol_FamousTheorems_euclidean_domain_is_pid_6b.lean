-- Prove2me | solution 1 for FamousTheorems.euclidean_domain_is_pid_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:03:54.58112+00:00
-- url     : https://prove2.me/submissions/3598e1b0-7586-4fac-9786-512227064908

import Mathlib

theorem solution (R : Type*) [EuclideanDomain R] : IsPrincipalIdealRing R :=
  EuclideanDomain.to_principal_ideal_domain
