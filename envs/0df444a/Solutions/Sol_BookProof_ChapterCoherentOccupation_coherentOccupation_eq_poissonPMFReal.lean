-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:11:00.803989+00:00
-- url     : https://prove2.me/submissions/d19de1e9-34db-4817-8137-e98fb57fc7f9

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.coherentOccupation_eq_poissonPMFReal
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (r : NNReal) (n : ℕ) :
    coherentOccupation r n = poissonPMFReal r n := rfl
