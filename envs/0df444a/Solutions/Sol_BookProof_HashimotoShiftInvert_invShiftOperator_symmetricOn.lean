-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.invShiftOperator_symmetricOn
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:11:04.696917+00:00
-- url     : https://prove2.me/submissions/21451c36-ddd0-4a71-b770-d5f1cb78eb2b

-- Generated from ChapterHashimotoShiftInvert.lean — theorem BookProof.HashimotoShiftInvert.invShiftOperator_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsFriedrichsLimit
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib

import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterFarisLavineCore
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
    (hR : IsSelfAdjoint R) :
    SymmetricOn (LinearMap.range (R : F →ₗ[ℂ] F)) (invShiftOperator R hinj γ) := by
  intro x y
  have hx : R (preim R (x : LinearMap.range (R : F →ₗ[ℂ] F))) = (x : F) := preim_spec _ _
  have hy : R (preim R (y : LinearMap.range (R : F →ₗ[ℂ] F))) = (y : F) := preim_spec _ _
  have hAx : invShiftOperator R hinj γ x = preim R x - (γ : ℂ) • (x : F) := rfl
  have hAy : invShiftOperator R hinj γ y = preim R y - (γ : ℂ) • (y : F) := rfl
  rw [hAx, hAy]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  have hstar : ContinuousLinearMap.adjoint R = R := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact IsSelfAdjoint.star_eq hR
  have hswap : inner ℂ (preim R x) (y : F) = inner ℂ (x : F) (preim R y) := by
    have hAd := ContinuousLinearMap.adjoint_inner_left R (preim R y) (preim R x)
    rw [hstar] at hAd
    calc
      inner ℂ (preim R x) (y : F)
          = inner ℂ (preim R x) (R (preim R y)) := by rw [hy]
      _ = inner ℂ (R (preim R x)) (preim R y) := hAd.symm
      _ = inner ℂ (x : F) (preim R y) := by rw [hx]
  rw [hswap]
