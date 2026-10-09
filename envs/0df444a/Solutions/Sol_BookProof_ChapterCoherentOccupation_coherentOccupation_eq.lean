-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:11:13.998873+00:00
-- url     : https://prove2.me/submissions/25323e74-5713-44c5-8ccb-cc0c8852b191

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_eq
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) (n : ℕ) :
    coherentOccupation lam n = Real.exp (-lam) * (lam ^ n / (n ! : ℝ)) := by

  rw [coherentOccupation, mul_div_assoc]
