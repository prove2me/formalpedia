-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:01:56.921993+00:00
-- url     : https://prove2.me/submissions/8a088f5c-a7dc-4ef9-ba84-4b37a8b810e0

-- Generated from ChapterFreeFieldBornSignOrientation.lean — solution of BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_one_iff
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_det_flipMatrix
open BookProof.ChapterFreeFieldBornSignOrientation



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    Matrix.det (flipMatrix b) = 1 ↔ Even (flipCount b) := by

  rw [det_flipMatrix]
  exact neg_one_pow_eq_one_iff_even (by norm_num)
