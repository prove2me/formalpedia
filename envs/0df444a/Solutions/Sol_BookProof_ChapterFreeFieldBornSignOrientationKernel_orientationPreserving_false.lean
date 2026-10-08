-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:05:15.711166+00:00
-- url     : https://prove2.me/submissions/dae737e1-7248-4dfb-abb7-165d5e667529

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — solution of BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_false
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_mem_specialOrthogonalGroup_iff
open BookProof.ChapterFreeFieldBornSignOrientationKernel



open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    flipMatrix (fun _ => false : Fin n → Bool) ∈
      Matrix.specialOrthogonalGroup (Fin n) ℝ := by

  rw [flipMatrix_mem_specialOrthogonalGroup_iff]
  simp [flipCount]
