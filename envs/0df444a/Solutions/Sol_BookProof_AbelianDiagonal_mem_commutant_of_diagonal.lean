-- Prove2me | solution 1 for BookProof.AbelianDiagonal.mem_commutant_of_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:48:14.198118+00:00
-- url     : https://prove2.me/submissions/ccad88b5-ea7e-4e63-a971-50259e72ebd1

import Mathlib
import Definitions.Def_ChapterAbelianDiagonal

open Matrix BookProof.AbelianDiagonal

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem solution (e : n → ℂ) (d : n → ℂ) :
    Matrix.diagonal e * Matrix.diagonal d = Matrix.diagonal d * Matrix.diagonal e := by
  simp [Matrix.diagonal_mul_diagonal, mul_comm]
