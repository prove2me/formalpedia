-- Prove2me | solution 1 for FamousTheorems.dedekind_ideal_unique_factorization_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:05:21.480273+00:00
-- url     : https://prove2.me/submissions/6b92a48f-19b6-403c-88f7-cb3eb59d306f

import Mathlib

theorem solution (A : Type*) [CommRing A] [IsDedekindDomain A] : UniqueFactorizationMonoid (Ideal A) :=
  Ideal.uniqueFactorizationMonoid
