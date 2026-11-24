-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.chord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:33:29.2198+00:00
-- url     : https://prove2.me/submissions/82cb2f15-7e9e-4764-a6da-d029b6f479bf

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_X_mul
import Theorems.Thm_Formalism_L2_Th1_A_Plus_xL_eq
import Theorems.Thm_Formalism_L2_Th1_A_Plus_yL_eq
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_tS
import Theorems.Thm_Formalism_L2_Th1_A_Plus_yL_sub
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_tS_mul
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_nS
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_xPlus
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_yPlus
import Theorems.Thm_Formalism_L2_Th1_A_Plus_equation_C
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_chordFormula
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
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
open Formalism.L2.Th1.A.Plus
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)
namespace Formalism.L2.Th1.A.Plus
theorem _root_.solution (hFL : FlowL.{u}) {xP yP : R} (hP : W.toAffine.Equation xP yP) :
    toL (xPlus W xP yP) = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) ∧
    toL (yPlus W xP yP)
      = (curveL W).toAffine.addY (xL W) (HahnSeries.C xP) (yL W) (slopeL W xP yP) := by
  obtain ⟨hX, hY⟩ := chordFormula _ (curveL W) (xL W) (yL W) (HahnSeries.C xP)
    (HahnSeries.C yP) (toL (tS W xP)) (hFL R W).1.1 (equation_C W hP) (toL_tS_mul W xP)
  have h : (toL X : LaurentSeries R) * uPow (-1) = 1 := toL_X_mul
  have hx : toL (xPlus W xP yP)
      = (curveL W).toAffine.addX (xL W) (HahnSeries.C xP) (slopeL W xP yP) := by
    rw [slopeL, hX, toL_xPlus, toL_nS, toL_tS, xL_eq, yL_eq]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_add, map_sub, map_mul, map_pow,
      map_ofNat]
    generalize toL (invOfUnit (tDen W xP) 1) = v
    generalize toL (xS W) = xs
    generalize toL (yS W) = ys
    linear_combination (-(HahnSeries.C W.a₄ - HahnSeries.C W.a₁ * HahnSeries.C yP
        + 2 * HahnSeries.C W.a₂ * HahnSeries.C xP + 3 * HahnSeries.C xP ^ 2) * xs * v ^ 2
          * toL X ^ 2 * (toL X * uPow (-1) + 1)
      + (2 * HahnSeries.C yP + HahnSeries.C W.a₁ * HahnSeries.C xP + HahnSeries.C W.a₃) * ys
          * v ^ 2 * toL X * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h
  refine ⟨hx, ?_⟩
  rw [slopeL] at hx ⊢
  rw [hY, ← hx, toL_yPlus, yL_sub, toL_tS]
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  rw [toL_xPlus]
  linear_combination (toL (yS W - C yP * X ^ 3) * toL (nS W xP yP)
    * toL (invOfUnit (tDen W xP) 1) ^ 3 * ((toL X * uPow (-1)) ^ 2 + toL X * uPow (-1) + 1)) * h
end Formalism.L2.Th1.A.Plus
