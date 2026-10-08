-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:02:31.289494+00:00
-- url     : https://prove2.me/submissions/e68ed41a-6d7a-4a81-85ab-367aa0644758

-- Generated from ChapterFreeFieldBornSignOrientation.lean — solution of BookProof.ChapterFreeFieldBornSignOrientation.det_flipMatrix_eq_neg_one_iff
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
    Matrix.det (flipMatrix b) = -1 ↔ Odd (flipCount b) := by

  rw [det_flipMatrix]
  exact neg_one_pow_eq_neg_one_iff_odd (by norm_num)
