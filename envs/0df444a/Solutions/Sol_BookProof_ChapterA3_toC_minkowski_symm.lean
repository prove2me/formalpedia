-- Prove2me | solution 1 for BookProof.ChapterA3.toC_minkowski_symm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T15:34:13.595211+00:00
-- url     : https://prove2.me/submissions/4086779d-94b4-417d-9022-fa3e5180d15d

-- Generated from ChapterA3h.lean — solution of BookProof.ChapterA3.toC_minkowski_symm
import Mathlib
import Definitions.Def_ChapterA3h
open BookProof.ChapterA3



open Matrix
open scoped ComplexConjugate

set_option maxHeartbeats 1000000 in
theorem solution : (toC minkowskiMat)ᵀ = toC minkowskiMat := by

  ext i j; simp only [toC, transpose_apply, map_apply, Complex.ofReal_inj] ;
  fin_cases i <;> fin_cases j <;> rfl
