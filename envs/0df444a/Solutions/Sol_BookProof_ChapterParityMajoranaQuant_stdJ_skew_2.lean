-- Prove2me | solution 2 for BookProof.ChapterParityMajoranaQuant.stdJ_skew
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-08T02:21:31.288511+00:00
-- url     : https://prove2.me/submissions/bbb5b7a6-aa2f-4843-bd87-69cf442319d6

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
