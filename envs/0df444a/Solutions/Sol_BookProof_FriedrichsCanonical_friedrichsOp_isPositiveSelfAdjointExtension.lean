-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:38:29.042986+00:00
-- url     : https://prove2.me/submissions/459df8d2-6151-40aa-afeb-e4d6ce4e2c71

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.friedrichsOp_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Theorems.Thm_BookProof_HashimotoShiftInvert_invShiftOperator_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_FriedrichsExtension_FormDom_dom_le_range
import Theorems.Thm_BookProof_FriedrichsExtension_FormDom_friedrichsResolvent_shift
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.YangMillsFriedrichs
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open BookProof.FriedrichsCanonical in
theorem solution (P : PosSymOp F)
    (hdense : Dense (P.dom : Set F)) :
    IsPositiveSelfAdjointExtension P.op (friedrichsOp P hdense) := by
  refine invShiftOperator_isPositiveSelfAdjointExtension (friedrichsResolvent P)
    (friedrichsResolvent_injective P hdense) 1 (friedrichsResolvent_isSelfAdjoint P)
    (friedrichsResolvent_pos P) (dom_le_range P) P.op ?_
  intro x
  rw [invShiftOperator_apply, preim_eq _ (friedrichsResolvent_injective P hdense) _
    (friedrichsResolvent_shift P x)]
  simp
