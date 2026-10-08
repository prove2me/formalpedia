-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:13:47.578247+00:00
-- url     : https://prove2.me/submissions/d360cf1c-9318-46d3-a359-c1bb6b344206

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — solution of BookProof.ChapterFreeFieldBornSignOrientationKernel.orientationPreserving_xor_iff
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationKernel_even_flipCount_xor_iff
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_mem_specialOrthogonalGroup_iff
open BookProof.ChapterFreeFieldBornSignOrientationKernel



open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b₁ b₂ : Fin n → Bool) :
    flipMatrix (fun k => xor (b₁ k) (b₂ k)) ∈
        Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
      (flipMatrix b₁ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ ↔
       flipMatrix b₂ ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ) := by

  rw [flipMatrix_mem_specialOrthogonalGroup_iff,
    flipMatrix_mem_specialOrthogonalGroup_iff,
    flipMatrix_mem_specialOrthogonalGroup_iff, even_flipCount_xor_iff]
