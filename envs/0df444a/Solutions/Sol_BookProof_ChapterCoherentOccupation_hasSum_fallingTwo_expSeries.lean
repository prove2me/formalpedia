-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:12:07.507655+00:00
-- url     : https://prove2.me/submissions/bd1928bd-c129-4a42-b6ab-78e5d7f3cd4c

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.hasSum_fallingTwo_expSeries
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_expSeries
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (lam ^ n / (n ! : ℝ)))
      (lam ^ 2 * Real.exp lam) := by

  have key : HasSum (fun n : ℕ => ((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1) *
      (lam ^ (n + 2) / (((n + 2)! : ℕ) : ℝ))) (lam ^ 2 * Real.exp lam) := by
    refine ((hasSum_expSeries lam).mul_left (lam ^ 2)).congr_fun ?_
    intro n
    rw [Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have hshift := (hasSum_nat_add_iff
    (f := fun n : ℕ => (n : ℝ) * ((n : ℝ) - 1) * (lam ^ n / (n ! : ℝ))) 2).mp key
  simpa [Finset.sum_range_succ] using hshift
