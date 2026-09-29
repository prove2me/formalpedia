-- Prove2me | solution 1 for FamousTheorems.mv_polynomial_ufd_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:09:33.042074+00:00
-- url     : https://prove2.me/submissions/8055cabf-c838-44f5-b47a-ad60dabe2911

import Mathlib

theorem solution (σ : Type*) {D : Type*} [CommRing D] [UniqueFactorizationMonoid D] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  MvPolynomial.uniqueFactorizationMonoid σ
