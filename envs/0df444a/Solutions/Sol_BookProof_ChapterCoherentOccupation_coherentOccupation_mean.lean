-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_mean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:12:46.214925+00:00
-- url     : https://prove2.me/submissions/07c67d20-c68f-462f-8367-5b090c03dfd5

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_mean
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
import Theorems.Thm_BookProof_ChapterCoherentOccupation_coherentOccupation_hasSum_mean
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) :
    ∑' n : ℕ, (n : ℝ) * coherentOccupation lam n = lam := (coherentOccupation_hasSum_mean lam).tsum_eq
