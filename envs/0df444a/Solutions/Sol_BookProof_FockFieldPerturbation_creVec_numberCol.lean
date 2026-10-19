-- Prove2me | solution 1 for BookProof.FockFieldPerturbation.creVec_numberCol
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T01:00:50.042018+00:00
-- url     : https://prove2.me/submissions/476b6929-3257-4fc8-8d9b-38c851cc1bc8

import Definitions.Def_ChapterFockNumberPreservingGap
import Definitions.Def_ChapterFockInteractionStability
import Mathlib
import Definitions.Def_ChapterFockFieldPerturbation
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
-- Generated from ChapterFockFieldPerturbation.lean — theorem BookProof.FockFieldPerturbation.creVec_numberCol
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.FockFieldPerturbation


noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FockNumberPreservingGap BookProof.FockInteractionStability


theorem solution (k : ℕ) (x : FockAlg) : creVec (numberCol k) x = creA k x := by
  simp [creVec, numberCol, diagCol]

