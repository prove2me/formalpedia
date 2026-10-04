-- Prove2me | solution 1 for BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_apply
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:49:30.010277+00:00
-- url     : https://prove2.me/submissions/a624f582-089c-4645-acb9-8f0bc73a16f0

-- Generated from ChapterFriedrichsExtension.lean — theorem BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp


set_option linter.unusedSectionVars false

theorem solution (P : PosSymOp F) (u v : F) :
    (inner ℂ u (friedrichsResolvent P v) : ℂ) =
      inner ℂ (formRiesz P u) (formRiesz P v) := by
  have hR : (friedrichsResolvent P v : F) = formExt P (formRiesz P v) := by
    simp [friedrichsResolvent, LinearMap.mkContinuous_apply]
  rw [hR]
  exact (formRiesz_spec P u (formRiesz P v)).symm
