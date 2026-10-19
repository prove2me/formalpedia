-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:07.514935+00:00
-- url     : https://prove2.me/submissions/126934d3-82db-4379-8d6e-d468c68a9852

-- Generated from ChapterFreeFieldBornSignRepresentation.lean — solution of BookProof.ChapterFreeFieldBornSignRepresentation.flipMatrix_injective
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignRepresentation
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignHom_flipVec_injective
import Definitions.Def_ChapterFreeFieldBornSignAction
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Definitions.Def_ChapterFreeFieldBornSignOrientation
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignRepresentation



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution : Function.Injective (flipMatrix :
    (Fin n → Bool) → Matrix (Fin n) (Fin n) ℝ) := by

  intro b₁ b₂ h
  apply flipVec_injective
  ext k
  convert congrArg (fun m : Matrix (Fin n) (Fin n) ℝ => m k k) h using 1 <;>
    simp [flipMatrix]
