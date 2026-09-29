-- Prove2me | solution 1 for FamousTheorems.fundamental_theorem_symmetric_polynomials
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:34.179475+00:00
-- url     : https://prove2.me/submissions/52f45175-d922-409c-9d0a-0f761b73a2bc

import Mathlib

theorem solution (σ R : Type*) [Fintype σ] [CommRing R] {n : ℕ} (h : Fintype.card σ ≤ n) :
    Function.Surjective (MvPolynomial.esymmAlgHom σ R n) :=
  MvPolynomial.esymmAlgHom_surjective R h
