-- Prove2me | solution 1 for BookProof.AbelianDiagonal.diagonal_commute
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T05:49:36.26698+00:00
-- url     : https://prove2.me/submissions/5de9c584-d1fb-4f39-8579-55de3cba3d08

import Mathlib
import Definitions.Def_ChapterAbelianDiagonal
open Matrix BookProof.AbelianDiagonal
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution (d e : n → ℂ) :
    Matrix.diagonal d * Matrix.diagonal e = Matrix.diagonal e * Matrix.diagonal d := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

#print axioms solution

