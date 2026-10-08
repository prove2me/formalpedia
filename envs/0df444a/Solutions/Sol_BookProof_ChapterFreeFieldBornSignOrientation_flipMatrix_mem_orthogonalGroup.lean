-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_orthogonalGroup
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:59:32.109007+00:00
-- url     : https://prove2.me/submissions/5ee3e3ff-ff0b-48e8-b351-9b6607ecd1a5

-- Generated from ChapterFreeFieldBornSignOrientation.lean — solution of BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_orthogonalGroup
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_transpose
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_flipMatrix_sq
open BookProof.ChapterFreeFieldBornSignOrientation



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    flipMatrix b ∈ Matrix.orthogonalGroup (Fin n) ℝ := by

  rw [Matrix.mem_orthogonalGroup_iff, flipMatrix_transpose]
  exact flipMatrix_sq b
