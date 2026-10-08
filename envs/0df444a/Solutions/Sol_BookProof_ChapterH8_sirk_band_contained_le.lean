-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_band_contained_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:48:38.909822+00:00
-- url     : https://prove2.me/submissions/6168cc78-f8a3-41ae-b96e-689a467971cf

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_band_contained_le
import Mathlib
import Definitions.Def_ChapterH8
import Theorems.Thm_BookProof_ChapterH6_sirk_error_bound_antitone
open BookProof.ChapterH8



noncomputable section


open BookProof.ChapterH4 BookProof.ChapterH5 BookProof.ChapterH6

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution (C Dmin h nv : ℝ)
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) {m n : ℕ} (hmn : m ≤ n) :
    Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n)
      ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv m) := Set.Icc_subset_Icc le_rfl (sirk_error_bound_antitone C Dmin h nv hC hD hnv hh hmn)
