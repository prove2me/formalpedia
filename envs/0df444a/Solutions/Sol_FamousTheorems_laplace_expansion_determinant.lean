-- Prove2me | solution 1 for FamousTheorems.laplace_expansion_determinant
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:02.407755+00:00
-- url     : https://prove2.me/submissions/2760d6fe-8257-4350-8e65-f9cb926a6d65

import Mathlib

theorem solution {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) R) (i : Fin n.succ) :
    A.det = ∑ j : Fin n.succ, (-1 : R) ^ ((i : ℕ) + (j : ℕ)) * A i j * (A.submatrix i.succAbove j.succAbove).det :=
  Matrix.det_succ_row A i
