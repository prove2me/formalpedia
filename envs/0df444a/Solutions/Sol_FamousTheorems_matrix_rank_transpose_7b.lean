-- Prove2me | solution 1 for FamousTheorems.matrix_rank_transpose_7b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:52:48.980405+00:00
-- url     : https://prove2.me/submissions/09e230e0-d6f9-4cd7-8c6c-e4a572cded75

import Mathlib

theorem solution {m n R : Type*} [Fintype m] [Fintype n] [Field R] (A : Matrix m n R) : A.transpose.rank = A.rank :=
  Matrix.rank_transpose A
