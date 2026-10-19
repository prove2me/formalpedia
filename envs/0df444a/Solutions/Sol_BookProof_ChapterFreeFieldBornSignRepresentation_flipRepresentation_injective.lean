-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:08.595302+00:00
-- url     : https://prove2.me/submissions/310e9842-85ec-4dda-a4af-5a9afc0dbd85

-- Generated from ChapterFreeFieldBornSignRepresentation.lean — solution of BookProof.ChapterFreeFieldBornSignRepresentation.flipRepresentation_injective
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignRepresentation
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignRepresentation_flipMatrix_injective
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
theorem solution :
    Function.Injective (flipRepresentation n) := by

  intro b₁ b₂ h
  apply_fun fun x => x.val at h
  exact Multiplicative.toAdd.injective (flipMatrix_injective h)
