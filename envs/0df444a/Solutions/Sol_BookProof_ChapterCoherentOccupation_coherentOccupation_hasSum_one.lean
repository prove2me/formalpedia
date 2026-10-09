-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:11:27.911153+00:00
-- url     : https://prove2.me/submissions/f62ca3de-586f-4305-bdd6-8398cf4417a7

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_one
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_expSeries
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) : HasSum (coherentOccupation lam) 1 := by

  have h := (hasSum_expSeries lam).mul_left (Real.exp (-lam))
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
  exact h.congr_fun fun n => coherentOccupation_eq lam n
