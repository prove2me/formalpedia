-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:12:20.713981+00:00
-- url     : https://prove2.me/submissions/b07162f0-2262-4a5f-b487-14de33fcd0b0

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_hasSum_mean
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq
import Theorems.Thm_BookProof_ChapterCoherentOccupation_hasSum_mul_expSeries
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * coherentOccupation lam n) lam := by

  have h := (hasSum_mul_expSeries lam).mul_left (Real.exp (-lam))
  have hval : Real.exp (-lam) * (lam * Real.exp lam) = lam := by
    rw [show Real.exp (-lam) * (lam * Real.exp lam)
        = lam * (Real.exp (-lam) * Real.exp lam) by ring,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [coherentOccupation_eq]
  ring
