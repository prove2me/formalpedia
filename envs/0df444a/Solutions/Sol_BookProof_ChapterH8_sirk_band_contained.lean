-- Prove2me | solution 1 for BookProof.ChapterH8.sirk_band_contained
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T22:48:12.169987+00:00
-- url     : https://prove2.me/submissions/9efd8416-6386-4a1d-b066-cac14eda46b5

-- Generated from ChapterH8.lean — solution of BookProof.ChapterH8.sirk_band_contained
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
    (hC : 0 ≤ C) (hD : 0 ≤ Dmin) (hnv : 0 ≤ nv) (hh : 0 ≤ h) (n : ℕ) :
    Set.Icc (0 : ℝ) (sirkBound C Dmin h nv (n + 1))
      ⊆ Set.Icc (0 : ℝ) (sirkBound C Dmin h nv n) :=
  Set.Icc_subset_Icc le_rfl
      (sirk_error_bound_antitone C Dmin h nv hC hD hnv hh (Nat.le_succ n))
