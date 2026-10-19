-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.fieldVec_vac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:01:05.072984+00:00
-- url     : https://prove2.me/submissions/2c37bebe-b437-4d6f-ad8d-105336a07445

import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.fieldVec_vac
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability


theorem solution (k : ℕ) :
    fieldVec (Finsupp.single k 1) vac = Finsupp.single (Finsupp.single k 1) (1 : ℂ) := by
  simp [fieldVec, creVec, annVec, vac, annA, creA, up, dn]

