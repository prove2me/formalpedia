-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.up_confAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:51:51.309756+00:00
-- url     : https://prove2.me/submissions/6acc1487-2872-4fdb-aaca-8f85d30aa02d

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.up_confAt
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockSecondQuantization_up_of_ne
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k m : ℕ) : up k (confAt k m) = confAt k (m + 1) := by

  refine Finsupp.ext fun i => ?_
  rcases eq_or_ne i k with rfl | h
  · simp [up, confAt]
  · rw [up_of_ne _ h]
    simp [confAt, h]
