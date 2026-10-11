-- Prove2me | solution 1 for BookProof.ChapterTrajectory.finalProb_total
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:27.7181+00:00
-- url     : https://prove2.me/submissions/60407840-d17c-48f5-ac39-9957173eae75

-- Generated from ChapterTrajectory.lean — solution of BookProof.ChapterTrajectory.finalProb_total
import Mathlib
import Definitions.Def_ChapterTrajectory
import Theorems.Thm_BookProof_ChapterTrajectory_jointProb_sum_final_eq_midProb
import Theorems.Thm_BookProof_ChapterTrajectory_midProb_sum
open BookProof.ChapterTrajectory



open scoped BigOperators Matrix


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (U V : Matrix (Fin n) (Fin n) ℂ) (psi : Fin n → ℂ)
    (hU : Uᴴ * U = 1) (hV : Vᴴ * V = 1) (hpsi : ∑ a, ‖psi a‖ ^ 2 = 1) :
    ∑ f, finalProb U V psi f = 1 := by

  unfold finalProb
  rw [← hpsi, Finset.sum_comm]
  rw [← midProb_sum U psi hU,
    Finset.sum_congr rfl fun _ _ => jointProb_sum_final_eq_midProb U V psi hV _]
