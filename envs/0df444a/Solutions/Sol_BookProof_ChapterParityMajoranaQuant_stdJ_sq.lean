-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.stdJ_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:16:20.601722+00:00
-- url     : https://prove2.me/submissions/ae385546-3d59-426a-8c28-fec69edd44c6

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.stdJ_sq
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution : stdJ * stdJ = -1 := by

  unfold stdJ; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]
