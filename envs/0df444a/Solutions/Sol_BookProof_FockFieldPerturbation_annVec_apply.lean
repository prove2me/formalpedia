-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.annVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:59:56.199712+00:00
-- url     : https://prove2.me/submissions/a311505c-764b-4ba6-a686-b1eb1d0433aa

import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.annVec_apply
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability


theorem solution (f : ℕ →₀ ℂ) (x : FockAlg) :
    annVec f x = ∑ j ∈ f.support, ((starRingEnd ℂ) (f j)) • annA j x := by
  simp [annVec, LinearMap.sum_apply]

