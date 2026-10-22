-- Prove2me | solution 1 for BookProof.FockCubicUnbounded.confNumber_confAt
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T11:51:54.74781+00:00
-- url     : https://prove2.me/submissions/8755e0b0-b0a7-46a0-b0f2-7eadbab74348

-- Generated from ChapterFockCubicUnbounded.lean — solution of BookProof.FockCubicUnbounded.confNumber_confAt
import Mathlib
import Definitions.Def_ChapterFockCubicUnbounded
import Theorems.Thm_BookProof_FockCubicUnbounded_confAt_self
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
open BookProof.FockCubicUnbounded



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockFieldPerturbation
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization

set_option maxHeartbeats 1000000 in
theorem solution (k m : ℕ) : confNumber (confAt k m) = m := by

  classical
  rcases eq_or_ne m 0 with rfl | hm
  · simp [confAt, confNumber]
  · have hsupp : (confAt k m).support = {k} :=
      Finsupp.support_single_ne_zero k hm
    simp [confNumber, hsupp, confAt_self]
