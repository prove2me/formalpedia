-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T12:04:24.21013+00:00
-- url     : https://prove2.me/submissions/cfd591a4-c4a8-4229-89af-7951e2496799

-- Generated from ChapterFreeFieldBornSignOrientation.lean — solution of BookProof.ChapterFreeFieldBornSignOrientation.flipMatrix_mem_specialOrthogonalGroup_iff
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_mem_orthogonalGroup
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_det_flipMatrix_eq_one_iff
open BookProof.ChapterFreeFieldBornSignOrientation



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) :
    flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔ Even (flipCount b) := by

  rw [← det_flipMatrix_eq_one_iff b, Matrix.mem_specialOrthogonalGroup_iff]
  exact ⟨fun h => h.2, fun h => ⟨flipMatrix_mem_orthogonalGroup b, h⟩⟩
