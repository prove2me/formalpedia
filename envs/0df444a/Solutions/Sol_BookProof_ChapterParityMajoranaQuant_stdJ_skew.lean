-- Prove2me | solution 1 for BookProof.ChapterParityMajoranaQuant.stdJ_skew
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:21:07.310347+00:00
-- url     : https://prove2.me/submissions/a73b4e43-a8cd-47e8-ae95-78daced51f01

-- Generated from ChapterParityMajoranaQuant.lean — solution of BookProof.ChapterParityMajoranaQuant.stdJ_skew
import Mathlib
import Definitions.Def_ChapterParityMajoranaQuant
open BookProof.ChapterParityMajoranaQuant











open Matrix
open scoped ComplexConjugate


variable {m : ℕ}




variable (J : Matrix (Fin m) (Fin m) ℂ)

set_option maxHeartbeats 1000000 in
theorem solution : stdJᴴ = -stdJ := by

  unfold stdJ; ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, Matrix.neg_apply]
