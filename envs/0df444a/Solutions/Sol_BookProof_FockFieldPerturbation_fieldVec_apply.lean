-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.fieldVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:59:42.191732+00:00
-- url     : https://prove2.me/submissions/d2251655-0a7c-4361-8b46-1c5faecfc3cb

import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockSecondQuantization
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.fieldVec_apply
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability


theorem solution (f : ℕ →₀ ℂ) (x : FockAlg) :
    fieldVec f x = creVec f x + annVec f x := by
  rfl

