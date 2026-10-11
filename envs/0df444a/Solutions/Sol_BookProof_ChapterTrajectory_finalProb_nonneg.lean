-- Prove2me | solution 1 for BookProof.ChapterTrajectory.finalProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:21.681474+00:00
-- url     : https://prove2.me/submissions/23334046-bf2d-446d-88e2-7a34f0454c0e

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.finalProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
import Theorems.Thm_BookProof_ChapterTrajectory_jointProb_nonneg
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f : Fin n) : 0 ≤ finalProb U V psi f := Finset.sum_nonneg fun _ _ => jointProb_nonneg _ _ _ _ _
