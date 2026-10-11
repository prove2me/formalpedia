-- Prove2me | solution 1 for BookProof.ChapterTrajectory.condProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:22.875055+00:00
-- url     : https://prove2.me/submissions/b42dd51c-1856-49c4-bc89-9826b6d5f169

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.condProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
import Theorems.Thm_BookProof_ChapterTrajectory_jointProb_nonneg
import Theorems.Thm_BookProof_ChapterTrajectory_finalProb_nonneg
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f a : Fin n) : 0 ≤ condProb U V psi f a := div_nonneg (jointProb_nonneg _ _ _ _ _) (finalProb_nonneg _ _ _ _)
