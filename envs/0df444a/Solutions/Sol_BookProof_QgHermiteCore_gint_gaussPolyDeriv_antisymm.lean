-- Prove2me | solution 1 for BookProof.QgHermiteCore.gint_gaussPolyDeriv_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:22:25.542814+00:00
-- url     : https://prove2.me/submissions/ffd52d48-814f-47c4-bc25-2c9b50708e89

import Definitions.Def_ChapterHermiteFunctions
open BookProof.HermiteCore Polynomial
set_option autoImplicit false

theorem solution (p q : Polynomial ℝ) :
    gint ((derivative p - C (1 / 2) * X * p) * q) =
      - gint (p * (derivative q - C (1 / 2) * X * q)) := by
  have h := gint_ibp p q
  rw [mul_sub, gint_sub] at h
  rw [sub_mul, gint_sub, mul_sub, gint_sub]
  rw [show C (1 / 2) * X * p * q = C (1 / 2) * (p * (X * q)) by ring,
    show p * (C (1 / 2) * X * q) = C (1 / 2) * (p * (X * q)) by ring,
    gint_C_mul]
  linarith
#print axioms solution
