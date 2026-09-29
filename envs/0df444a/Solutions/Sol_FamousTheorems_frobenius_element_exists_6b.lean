-- Prove2me | solution 1 for FamousTheorems.frobenius_element_exists_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:05:13.874387+00:00
-- url     : https://prove2.me/submissions/95062df2-469f-4178-bea9-abef29ae3057

import Mathlib

theorem solution (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [Group G]
    [MulSemiringAction G S] [SMulCommClass G R S] (Q : Ideal S) [Finite G] [Algebra.IsInvariant R S G]
    [Q.IsPrime] [Finite (S ⧸ Q)] : ∃ σ : G, IsArithFrobAt R σ Q :=
  IsArithFrobAt.exists_of_isInvariant R G Q
