-- Prove2me | solution 1 for BookProof.ChapterParityChirality.chirality_iff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T09:12:50.830999+00:00
-- url     : https://prove2.me/submissions/fd3e5d2d-8f75-4d46-9131-db5844705229

-- Generated from ChapterParityChirality.lean — solution of BookProof.ChapterParityChirality.chirality_iff
import Mathlib
import Definitions.Def_ChapterParityChirality
import Theorems.Thm_BookProof_ChapterParityChirality_isigma3_sq
import Theorems.Thm_BookProof_ChapterParityChirality_igamma5_sq
import Theorems.Thm_BookProof_ChapterParityChirality_isigma3_igamma5
import Theorems.Thm_BookProof_ChapterParityChirality_igamma5_isigma3
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParitySU2
open BookProof.ChapterParityChirality



open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity
open BookProof.ChapterParitySU2

set_option maxHeartbeats 1000000 in
theorem solution (v : Fin 2 × Fin 4 → ℂ) :
    isigma3 *ᵥ v = igamma5 *ᵥ v ↔ chi *ᵥ v = -v := by

  constructor
  · intro h
    have hh := congr_arg (fun w => igamma5 *ᵥ w) h
    rw [Matrix.mulVec_mulVec, igamma5_isigma3, Matrix.mulVec_mulVec, igamma5_sq,
      Matrix.neg_mulVec, Matrix.one_mulVec] at hh
    exact hh
  · intro h
    have hh := congr_arg (fun w => isigma3 *ᵥ w) h
    rw [Matrix.mulVec_mulVec, ← isigma3_igamma5, ← Matrix.mul_assoc, isigma3_sq,
      neg_one_mul, Matrix.neg_mulVec, Matrix.mulVec_neg] at hh
    exact (neg_injective hh).symm
