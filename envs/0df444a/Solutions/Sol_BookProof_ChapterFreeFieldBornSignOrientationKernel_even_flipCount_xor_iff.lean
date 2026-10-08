-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:08:17.853074+00:00
-- url     : https://prove2.me/submissions/9beee952-4950-4594-b81d-c3d70b393d34

-- Generated from ChapterFreeFieldBornSignOrientationKernel.lean — solution of BookProof.ChapterFreeFieldBornSignOrientationKernel.even_flipCount_xor_iff
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationKernel
open BookProof.ChapterFreeFieldBornSignOrientationKernel



open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b₁ b₂ : Fin n → Bool) :
    Even (flipCount (fun k => xor (b₁ k) (b₂ k))) ↔
      (Even (flipCount b₁) ↔ Even (flipCount b₂)) := by

  unfold flipCount
  induction (Finset.univ : Finset (Fin n)) using Finset.induction <;>
    simp_all [Finset.filter_insert]
  grind
