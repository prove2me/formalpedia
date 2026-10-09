-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:11:54.165661+00:00
-- url     : https://prove2.me/submissions/89941c18-ce77-4d44-9a6b-9c2d6968ac86

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.hasSum_mul_expSeries
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_expSeries
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * (lam ^ n / (n ! : ℝ))) (lam * Real.exp lam) := by

  have key : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (lam ^ (n + 1) / (((n + 1)! : ℕ) : ℝ)))
      (lam * Real.exp lam) := by
    refine ((hasSum_expSeries lam).mul_left lam).congr_fun ?_
    intro n
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  simpa using
    (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * (lam ^ n / (n ! : ℝ))) 1).mp key
