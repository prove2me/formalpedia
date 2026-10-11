-- Prove2me | solution 1 for BookProof.ChapterTrajectory.jointProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:20.125814+00:00
-- url     : https://prove2.me/submissions/4b2b3aba-b9f3-4ede-a5b0-5088e903e8fe

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.jointProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
import Theorems.Thm_BookProof_ChapterTrajectory_midProb_nonneg
import Theorems.Thm_BookProof_ChapterTrajectory_transProb_nonneg
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f a : Fin n) : 0 ≤ jointProb U V psi f a := mul_nonneg (midProb_nonneg _ _ _) (transProb_nonneg _ _ _)
