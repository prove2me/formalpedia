-- Prove2me | solution 1 for FamousTheorems.galois_transitive_on_primes_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:02:12.505867+00:00
-- url     : https://prove2.me/submissions/6aacb945-4bb4-425d-8146-69ba9ca5b73d

import Mathlib

open scoped Pointwise

theorem solution (A B G : Type*) [CommRing A] [CommRing B] [Algebra A B] [Group G] [MulSemiringAction G B]
    [Algebra.IsInvariant A B G] [Finite G] [SMulCommClass G A B] (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
    (h : Ideal.under A P = Ideal.under A Q) : ∃ g : G, Q = g • P :=
  Algebra.IsInvariant.exists_smul_of_under_eq A B G P Q h
