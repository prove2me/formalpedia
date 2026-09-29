-- Prove2me | solution 1 for FamousTheorems.det_mul_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:52:22.23299+00:00
-- url     : https://prove2.me/submissions/3f9e5b0a-10ce-49d4-90af-baed63d91cb8

import Mathlib

theorem solution {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R] (M N : Matrix n n R) :
    (M * N).det = M.det * N.det :=
  Matrix.det_mul M N
