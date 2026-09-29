-- Prove2me | solution 1 for FamousTheorems.sylvester_determinant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:25:09.949923+00:00
-- url     : https://prove2.me/submissions/00499ee1-32f0-4077-a934-9c8d91bddfd7

import Mathlib

theorem solution {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing α] (A : Matrix m n α)
    (B : Matrix n m α) : (1 + A * B).det = (1 + B * A).det :=
  Matrix.det_one_add_mul_comm A B
