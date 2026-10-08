-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_false
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T11:39:34.133662+00:00
-- url     : https://prove2.me/submissions/37e7c82f-0117-4f73-80ad-2f46086a1aba

-- Generated from ChapterFreeFieldBornSignMatrix.lean — solution of BookProof.ChapterFreeFieldBornSignMatrix.flipMatrix_false
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignMatrix
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignHom_flipVec_false
open BookProof.ChapterFreeFieldBornSignMatrix



open BookProof.ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignHom


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution :
    flipMatrix (fun _ => false : Fin n → Bool) = 1 := by

  ext i j
  by_cases hi : i = j <;> simp_all [flipVec_false, flipMatrix]
  simp [hi, Matrix.one_apply]
