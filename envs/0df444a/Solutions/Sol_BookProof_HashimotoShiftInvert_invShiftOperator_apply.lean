-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.invShiftOperator_apply
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:11:03.16113+00:00
-- url     : https://prove2.me/submissions/86609807-6acb-4ac5-ae07-404f08e53bb5

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.invShiftOperator_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib

import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore

set_option linter.unusedSectionVars false
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology


theorem solution (R : F →L[ℂ] F) (hinj : Function.Injective R) (γ : ℝ)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) :
    invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := by
  rfl
