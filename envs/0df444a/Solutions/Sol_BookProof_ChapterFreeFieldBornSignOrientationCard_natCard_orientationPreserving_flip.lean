-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:05:11.238007+00:00
-- url     : https://prove2.me/submissions/d6f29887-c9ad-4d39-adee-889229ac4bba

-- Generated from ChapterFreeFieldBornSignOrientationCard.lean — solution of BookProof.ChapterFreeFieldBornSignOrientationCard.natCard_orientationPreserving_flip
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationCard
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientationCard_natCard_even_flip
import Theorems.Thm_BookProof_ChapterFreeFieldBornSignOrientation_flipMatrix_mem_specialOrthogonalGroup_iff
open BookProof.ChapterFreeFieldBornSignOrientationCard



open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignMatrix
open BookProof.ChapterFreeFieldBornSignOrientation

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) :
    Nat.card {b : Fin (n + 1) → Bool //
      flipMatrix b ∈ Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ} = 2 ^ n := by

  convert natCard_even_flip n using 3
  exact funext fun x => by rw [flipMatrix_mem_specialOrthogonalGroup_iff]
