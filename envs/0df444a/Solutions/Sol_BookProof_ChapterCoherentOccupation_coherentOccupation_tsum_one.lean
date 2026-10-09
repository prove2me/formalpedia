-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_tsum_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:11:40.954045+00:00
-- url     : https://prove2.me/submissions/0e808a47-07c2-4a22-992e-7b18685776db

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_tsum_one
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_hasSum_one
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) : ∑' n : ℕ, coherentOccupation lam n = 1 := (coherentOccupation_hasSum_one lam).tsum_eq
