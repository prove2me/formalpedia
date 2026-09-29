-- Prove2me | solution 1 for Diaz.det_add_two
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-08T07:15:40.630951+00:00
-- url     : https://prove2.me/submissions/217872be-785f-4753-a4c0-756f485da0a4

import Mathlib

open ComplexConjugate

theorem solution {R : Type*} [CommRing R] (X Y : Matrix (Fin 2) (Fin 2) R) :
    (X + Y).det = X.det + Y.det + Matrix.trace X * Matrix.trace Y - Matrix.trace (X * Y) := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  ring
