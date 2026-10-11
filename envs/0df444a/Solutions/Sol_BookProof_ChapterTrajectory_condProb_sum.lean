-- Prove2me | solution 1 for BookProof.ChapterTrajectory.condProb_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:29.04008+00:00
-- url     : https://prove2.me/submissions/78d310a7-af4f-4c8d-8ec0-5cf8704ee2c4

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.condProb_sum
import Mathlib
import Definitions.Def_ChapterTrajectory
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (f : Fin n) (hf : finalProb U V psi f ≠ 0) :
    ∑ a, condProb U V psi f a = 1 := by

  unfold condProb
  rw [← Finset.sum_div]
  exact div_self hf
