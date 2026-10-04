-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.shiftMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T14:44:56.461331+00:00
-- url     : https://prove2.me/submissions/f902c29c-fe03-4cd3-bb36-cfe5525230c6

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.shiftMap_apply
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterComplexShiftCore
open BookProof.HashimotoShiftInvert

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}



open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

theorem solution (A : Dom →ₗ[ℂ] F) (γ : ℝ) (x : Dom) :
    shiftMap A γ x = A x + (γ : ℂ) • (x : F) := by
  simp [shiftMap, LinearMap.add_apply, LinearMap.smul_apply]
