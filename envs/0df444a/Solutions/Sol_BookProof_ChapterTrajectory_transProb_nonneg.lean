-- Prove2me | solution 1 for BookProof.ChapterTrajectory.transProb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:18.72332+00:00
-- url     : https://prove2.me/submissions/50dac56b-a492-4a42-994d-8f3c97b64c3b

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.transProb_nonneg
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (V : Matrix (Fin n) (Fin n) ℂ) (f a : Fin n) :
    0 ≤ transProb V f a := by

  unfold transProb; positivity
