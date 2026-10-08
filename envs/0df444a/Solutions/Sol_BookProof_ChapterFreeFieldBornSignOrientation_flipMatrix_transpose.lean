-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:58:37.604176+00:00
-- url     : https://prove2.me/submissions/ba752f38-2691-4555-b82c-27deae8c0784

-- Generated from ChapterFreeFieldBornSignOrientation.lean — solution of BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_transpose
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientation



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    Matrix.transpose (flipMatrix b) = flipMatrix b := by

  exact Matrix.diagonal_transpose (flipVec b)
