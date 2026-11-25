-- Prove2me | solution 1 for Formalism.L2.Th1.A.addition_addition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:12:32.506574+00:00
-- url     : https://prove2.me/submissions/34c463d8-aa55-4040-9222-a0a520fc8dc9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FglInvariant
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_XPowSuccDvdOfDerivative
import Theorems.Thm_Formalism_L2_Th1_A_flow_unique
import Theorems.Thm_Formalism_L2_Th1_A_chord_equation
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_D_apply
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_flowTranslate
import Theorems.Thm_Formalism_L2_Th1_A_flowU
import Theorems.Thm_Formalism_L2_Th1_A_plusFlow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.L2.Th1.A.IsDer.toDerivation_apply
attribute [local simp] Formalism.L2.Th1.A.dLDR_apply
attribute [local simp] Formalism.L2.Th1.A.dLD_apply



set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Nn
namespace Formalism.L2.Th1.A
theorem _root_.solution : PlusPlus.{u} := by
  intro R _ W xP yP xQ yQ t hR hP hQ ht s hs
  obtain ⟨hDer, hConst, -, -, -, -⟩ := flowU R W
  obtain ⟨hFP, hxP0, hyP0⟩ := plusFlow R W xP yP hP
  have hPQ := chord_equation R W xP yP xQ yQ t hP hQ ht
  obtain ⟨hFS, hxS0, hyS0⟩ := plusFlow R W _ _ hPQ
  have hDC : ∀ r : R, D W (C r) = 0 := fun r => by
    rw [CurveSer.D_apply, derivative_C, mul_zero]
  have hQC : (curveS W).toAffine.Equation (C xQ) (C yQ) :=
    WeierstrassCurve.Affine.Equation.map (C : R →+* R⟦X⟧) hQ
  have hFT := flowTranslate _ (curveS W) (D W) (xPlus W xP yP) (yPlus W xP yP) (C xQ) (C yQ) s
    hDer hConst hFP hQC (hDC xQ) (hDC yQ) hs
  have hs0 : constantCoeff s = t := by
    have h := congrArg (constantCoeff (R := R)) hs
    rw [map_mul, map_sub, hxP0, constantCoeff_C, map_one] at h
    linear_combination t * h - constantCoeff s * ht
  refine flow_unique R W _ _ _ _ hR hFS hFT ?_ ?_
  · rw [hxS0]
    simp only [WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      map_add, map_sub, map_mul, map_pow, constantCoeff_C, hxP0, hyP0, hs0]
  · rw [hyS0]
    simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
      WeierstrassCurve.Affine.negY, WeierstrassCurve.Affine.addX, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      map_add, map_sub, map_neg, map_mul, map_pow, constantCoeff_C, hxP0, hyP0, hs0]
end Formalism.L2.Th1.A
