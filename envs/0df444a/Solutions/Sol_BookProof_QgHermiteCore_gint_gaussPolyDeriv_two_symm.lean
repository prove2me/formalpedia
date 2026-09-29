-- Prove2me | solution 1 for BookProof.QgHermiteCore.gint_gaussPolyDeriv_two_symm
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:16.442983+00:00
-- url     : https://prove2.me/submissions/10ccdaad-03a6-4fb4-8f26-fabf2c927e05

import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore Polynomial
set_option autoImplicit false

private theorem derivative_antisymmetry (p q : Polynomial ℝ) :
    gint ((derivative p - C (1 / 2) * X * p) * q) =
      - gint (p * (derivative q - C (1 / 2) * X * q)) := by
  have h := gint_ibp p q
  rw [mul_sub, gint_sub] at h
  rw [sub_mul, gint_sub, mul_sub, gint_sub]
  rw [show C (1 / 2) * X * p * q = C (1 / 2) * (p * (X * q)) by ring,
    show p * (C (1 / 2) * X * q) = C (1 / 2) * (p * (X * q)) by ring,
    gint_C_mul]
  linarith


theorem solution (p q : Polynomial ℝ) :
    gint (((derivative (derivative p - C (1 / 2) * X * p) -
      C (1 / 2) * X * (derivative p - C (1 / 2) * X * p))) * q) =
      gint (p * (derivative (derivative q - C (1 / 2) * X * q) -
        C (1 / 2) * X * (derivative q - C (1 / 2) * X * q))) := by
  rw [derivative_antisymmetry, derivative_antisymmetry, neg_neg]
#print axioms solution
