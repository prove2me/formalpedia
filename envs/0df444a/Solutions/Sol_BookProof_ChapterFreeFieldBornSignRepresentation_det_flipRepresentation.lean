-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:11.114321+00:00
-- url     : https://prove2.me/submissions/09988d96-9560-41a9-a364-dbeca27c101a

-- Generated from ChapterFreeFieldBornSignRepresentation.lean — solution of BookProof.ChapterFreeFieldBornSignRepresentation.det_flipRepresentation
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignRepresentation
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignMatrix_det_flipMatrix
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
theorem solution (b : Multiplicative (Fin n → Bool)) :
    Matrix.det (flipRepresentation n b : Matrix (Fin n) (Fin n) ℝ) =
      (-1 : ℝ) ^ flipCount b.toAdd := by

  exact det_flipMatrix b.toAdd
