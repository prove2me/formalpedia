-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:41:13.807923+00:00
-- url     : https://prove2.me/submissions/058a7b2a-5cc9-486a-b926-5ff478604928

-- Generated from ChapterFreeFieldBornSignMatrix.lean — solution of BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_sq
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignMatrix



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    flipMatrix b * flipMatrix b = 1 := by

  ext i j
  by_cases hi : i = j <;> simp_all [flipMatrix, flipVec]
  simp [hi, Matrix.one_apply]
