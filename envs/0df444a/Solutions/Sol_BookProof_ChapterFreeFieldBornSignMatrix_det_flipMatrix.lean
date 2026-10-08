-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:58:22.929351+00:00
-- url     : https://prove2.me/submissions/77405372-6a81-400c-813d-66474e65e632

-- Generated from ChapterFreeFieldBornSignMatrix.lean — solution of BookProof.ChapterFreeFieldBornSignMatrix.det_flipMatrix
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignHom_flipVec_prod
open BookProof.ChapterFreeFieldBornSignMatrix



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    Matrix.det (flipMatrix b) = (-1 : ℝ) ^ flipCount b := by

  convert flipVec_prod b using 1
  exact Matrix.det_diagonal
