-- Prove2me | solution 1 for BookProof.FriedrichsCanonical.dom_le_formDomain
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:38:21.766038+00:00
-- url     : https://prove2.me/submissions/2c4fc5cc-a629-47be-9398-4700bc38ef2f

-- Generated from ChapterFriedrichsCanonical.lean — theorem BookProof.FriedrichsCanonical.dom_le_formDomain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Mathlib
import Definitions.Def_ChapterFriedrichsCanonical
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom
open BookProof.QgOuterFockFL
open BookProof.FriedrichsCanonical



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
open BookProof.FriedrichsCanonical in
theorem solution (P : PosSymOp F) : P.dom ≤ formDomain P := by
  intro x hx
  exact ⟨((show FormDom P from ⟨x, hx⟩ : FormDom P) : FormSpace P), by
    rw [ContinuousLinearMap.coe_coe, formExt_coe]; rfl⟩
