-- Prove2me | solution 1 for FamousTheorems.schur_complement_determinant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:15.933449+00:00
-- url     : https://prove2.me/submissions/33a35f61-b489-492e-9814-17afc70b3cf5

import Mathlib

theorem solution {m n α : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [CommRing α] (A : Matrix m m α)
    (B : Matrix m n α) (C : Matrix n m α) (D : Matrix n n α) [Invertible A] :
    (Matrix.fromBlocks A B C D).det = A.det * (D - C * ⅟A * B).det :=
  Matrix.det_fromBlocks₁₁ A B C D
