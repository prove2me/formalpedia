-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:12:47.328479+00:00
-- url     : https://prove2.me/submissions/5a2ff027-dfd2-4fc1-9e25-8dca5eaecd76

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_second_moment
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq
import Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_fallingTwo_expSeries
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_hasSum_mean
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) ^ 2 * coherentOccupation lam n) (lam ^ 2 + lam) := by

  have hfall := (hasSum_fallingTwo_expSeries lam).mul_left (Real.exp (-lam))
  have hmean := coherentOccupation_hasSum_mean lam
  have hval : Real.exp (-lam) * (lam ^ 2 * Real.exp lam) = lam ^ 2 := by
    rw [show Real.exp (-lam) * (lam ^ 2 * Real.exp lam)
        = lam ^ 2 * (Real.exp (-lam) * Real.exp lam) by ring,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [hval] at hfall
  have hfall' : HasSum
      (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * coherentOccupation lam n) (lam ^ 2) := by
    refine hfall.congr_fun fun n => ?_
    rw [coherentOccupation_eq]
    ring
  refine (hfall'.add hmean).congr_fun fun n => ?_
  ring
