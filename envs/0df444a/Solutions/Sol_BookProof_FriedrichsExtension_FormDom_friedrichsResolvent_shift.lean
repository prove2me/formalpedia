-- Prove2me | solution 1 for BookProof.FriedrichsExtension.FormDom.friedrichsResolvent_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:20:00.217784+00:00
-- url     : https://prove2.me/submissions/c661eca3-6113-41f0-be5d-829af6f2dd44

import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Mathlib
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockFarisLavine

set_option autoImplicit false

universe u

section P2MHelpers

open BookProof.QgOuterFockFL
open BookProof.FriedrichsExtension
open BookProof.FriedrichsExtension.FormDom

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable [CompleteSpace F]

open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert
open BookProof.HermiteGalerkin
open scoped InnerProductSpace ENNReal lp

theorem p2m_formExt_coe (P : PosSymOp F) (z : FormDom P) :
    formExt P (z : FormSpace P) = toAmbient z := by
  have hu : IsUniformInducing (UniformSpace.Completion.toComplL (𝕜 := ℂ) (E := FormDom P)) := by
    rw [UniformSpace.Completion.coe_toComplL]
    exact UniformSpace.Completion.isUniformInducing_coe _
  have h := ContinuousLinearMap.extend_eq (f := incl P)
    (denseRange_toComplL P) hu z
  rw [UniformSpace.Completion.coe_toComplL] at h
  exact h

end P2MHelpers

open BookProof.FriedrichsExtension BookProof.FriedrichsExtension.FormDom in
theorem solution {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (P : PosSymOp F) (x : P.dom) :
    friedrichsResolvent P ((x : F) + P.op x) = (x : F) := by
  let y : FormDom P := x
  have hR : formRiesz P ((x : F) + P.op x) = (y : FormSpace P) := by
    refine ext_inner_right ℂ (fun k => ?_)
    rw [formRiesz_spec]
    induction k using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const.inner (formExt P).continuous)
        (continuous_const.inner continuous_id)
    | ih z =>
      rw [p2m_formExt_coe, UniformSpace.Completion.inner_coe, inner_def, inner_add_left]
      congr 1
      exact P.sym x (toDom z)
  show formExt P (formRiesz P ((x : F) + P.op x)) = (x : F)
  rw [hR, p2m_formExt_coe]
  rfl
