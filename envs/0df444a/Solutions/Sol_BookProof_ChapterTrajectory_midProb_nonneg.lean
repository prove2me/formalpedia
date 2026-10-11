-- Prove2me | solution 1 for BookProof.ChapterTrajectory.midProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:17.155997+00:00
-- url     : https://prove2.me/submissions/1c3087e4-b056-4e89-8af9-36fb5bfd896e

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.midProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (a : Fin n) : 0 ≤ midProb U psi a := by

  unfold midProb; positivity
