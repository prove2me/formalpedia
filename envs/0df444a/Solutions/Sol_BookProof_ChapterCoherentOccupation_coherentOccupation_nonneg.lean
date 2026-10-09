-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:11:15.085335+00:00
-- url     : https://prove2.me/submissions/4eac31cd-1338-46f4-8f1c-3555c8c49cb7

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_nonneg
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_eq
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution {lam : ℝ} (h : 0 ≤ lam) (n : ℕ) :
    0 ≤ coherentOccupation lam n := by

  rw [coherentOccupation_eq]
  positivity
