-- Prove2me | solution 1 for BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:25.355295+00:00
-- url     : https://prove2.me/submissions/17d37e1c-0812-47d2-a074-b40ebb1a8c96

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.jointProb_sum_final_eq_midProb
import Mathlib
import Definitions.Def_ChapterTrajectory
import Theorems.Thm_BookProof_ChapterTrajectory_transProb_sum
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ)
    (psi : Fin n → ℂ) (hV : Vᴴ * V = 1) (a : Fin n) :
    ∑ f, jointProb U V psi f a = midProb U psi a := by

  convert congr_arg (fun x : ℝ => midProb U psi a * x) (transProb_sum V hV a) using 1
  · unfold jointProb; rw [Finset.mul_sum]
  · ring
