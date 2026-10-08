-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_transpose_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:42:07.061988+00:00
-- url     : https://prove2.me/submissions/444f6c72-dd3f-47ac-82da-fb5f94ca1866

-- Generated from ChapterFreeFieldBornSignMatrix.lean — solution of BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_transpose_mul
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_sq
open BookProof.ChapterFreeFieldBornSignMatrix



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    Matrix.transpose (flipMatrix b) * flipMatrix b = 1 := by

  convert flipMatrix_sq b using 1
  unfold flipMatrix
  aesop
