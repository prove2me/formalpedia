-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.preim_eq
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:11:03.968767+00:00
-- url     : https://prove2.me/submissions/5b3474d7-ae22-4467-821f-3ee7660af57a

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.preim_eq
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


theorem solution (R : F →L[ℂ] F) (hinj : Function.Injective R)
    (y : LinearMap.range (R : F →ₗ[ℂ] F)) {u : F} (hu : R u = (y : F)) : preim R y = u := by
  apply hinj
  rw [BookProof.HashimotoShiftInvert.preim_spec, hu]
