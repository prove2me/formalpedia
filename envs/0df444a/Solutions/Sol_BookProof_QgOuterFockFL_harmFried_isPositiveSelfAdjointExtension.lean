-- Prove2me | solution 1 for BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T07:40:25.965011+00:00
-- url     : https://prove2.me/submissions/d38b86bc-9b2c-4748-9b85-c151fab98722

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterYangMillsFriedrichs
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
-- Generated from ChapterQgOuterFockFarisLavine.lean — theorem BookProof.QgOuterFockFL.harmFried_isPositiveSelfAdjointExtension
open BookProof.HermiteProductCore
open BookProof.QgHermiteOscillator
open BookProof.YangMillsFriedrichs
open BookProof.QgOuterFockFL


open scoped ENNReal


open BookProof.FarisLavine
open BookProof.DirectSumEsa
open BookProof.QgOuterFock
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.HashimotoShiftInvert
open BookProof.QgHermiteOscillator
open BookProof.HermiteProductCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable (C : ∀ i, Comparison (G i))
variable (H : ∀ i, (C i).dom →ₗ[ℂ] G i)
variable {C H}


theorem solution (d : ℕ) :
    IsPositiveSelfAdjointExtension (BookProof.QgOuterFockFL.harmCore (d := d)) (harmFried d).op := by
  exact BookProof.QgOuterFockFL.Comparison.isPositiveSelfAdjointExtension (harmFried d) _
    (fun x => BookProof.QgOuterFockFL.friedrichsComparison_extends (harmPosSym d) _ x)

