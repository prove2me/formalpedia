-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.numberCol_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:16:21.936537+00:00
-- url     : https://prove2.me/submissions/0a622b23-0b39-4c32-91ce-535771c04183

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.numberCol_eq
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) : numberCol k = Finsupp.single k (1 : ℂ) := by

  simp [numberCol, diagCol]
