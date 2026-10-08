-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:37:59.013919+00:00
-- url     : https://prove2.me/submissions/3cda771e-e9b5-438c-acbb-f24182ebd3aa

-- Generated from ChapterFreeFieldBornSignMatrix.lean — solution of BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_mulVec
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignMatrix



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    (flipMatrix b).mulVec x = boolFlip b x := by

  unfold boolFlip flipMatrix Matrix.mulVec
  aesop
