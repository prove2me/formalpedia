-- Prove2me | solution 1 for FamousTheorems.sophie_germain_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T07:27:39.941238+00:00
-- url     : https://prove2.me/submissions/4f3739cf-d52c-4009-b6f3-c00904f29eab

import Mathlib

theorem solution {R : Type*} [CommRing R] (a b : R) :
    a ^ 4 + 4 * b ^ 4 = ((a - b) ^ 2 + b ^ 2) * ((a + b) ^ 2 + b ^ 2) :=
  pow_four_add_four_mul_pow_four
