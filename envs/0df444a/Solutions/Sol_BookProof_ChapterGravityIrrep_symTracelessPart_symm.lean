-- Prove2me | solution 1 for BookProof.ChapterGravityIrrep.symTracelessPart_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:51:26.573111+00:00
-- url     : https://prove2.me/submissions/02dc079d-7210-48d3-9360-1b2701f5eee8

-- Generated from ChapterGravityIrrep.lean — solution of BookProof.ChapterGravityIrrep.symTracelessPart_symm
import Mathlib
import Definitions.Def_ChapterGravityIrrep
open BookProof.ChapterGravityIrrep




open Matrix
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin 3) (Fin 3) ℝ) :
    (symTracelessPart M)ᵀ = symTracelessPart M := by

  simp [symTracelessPart, transpose_sub, transpose_add, transpose_transpose, transpose_smul,
    Matrix.transpose_one]
  abel
