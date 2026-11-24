-- Prove2me | solution 1 for Formalism.L2.Th1.A.two_torsion_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:28:53.748143+00:00
-- url     : https://prove2.me/submissions/2b6d765b-7b0d-4678-9358-d8ad1331dc6b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
import Theorems.Thm_Formalism_L2_Th1_A_Plus_equation_C
import Theorems.Thm_Formalism_L2_Th1_A_Plus_toL_tS_mul
import Theorems.Thm_Formalism_L2_Th1_A_dLDR_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLD_apply
import Theorems.Thm_Formalism_L2_Th1_A_dLSpec
import Theorems.Thm_Formalism_L2_Th1_A_flowL
import Theorems.Thm_Formalism_L2_Th1_A_flowTwoTorsion
import Theorems.Thm_Formalism_L2_Th1_A_plusChord
import Theorems.Thm_Formalism_L2_Th1_A_toL_injective
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
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
namespace Formalism.L2.Th1.A
theorem _root_.solution : TwoTorsionU.{u} := by
  intro R _ W xT yT hT h2
  obtain ⟨hDer, hConst, hC, hD⟩ := dLSpec R W
  have hx := (plusChord R W xT yT hT).1
  have h2' : 2 * (HahnSeries.C yT : LaurentSeries R) + (curveL W).a₁ * HahnSeries.C xT
      + (curveL W).a₃ = 0 := by
    have h := congrArg (HahnSeries.C : R →+* LaurentSeries R) h2
    simpa only [map_add, map_mul, map_ofNat, map_zero, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃] using h
  obtain ⟨a, b, c⟩ := flowTwoTorsion _ (curveL W) (DL W) (xL W) (yL W) (HahnSeries.C xT)
    (HahnSeries.C yT) (toL (tS W xT)) hDer hConst (flowL R W).1 (Plus.equation_C W hT) (hC xT)
    (hC yT) h2' (Plus.toL_tS_mul W xT)
  rw [hD] at b c
  rw [hD] at c
  refine ⟨?_, ?_, ?_⟩
  · apply toL_injective
    rw [hx, slopeL, a]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, toL_C, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
  · apply toL_injective
    rw [map_pow, b]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, toL_C, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_b₂]
  · apply toL_injective
    rw [c]
    simp only [map_add, map_sub, map_mul, map_pow, map_ofNat, toL_C, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, WeierstrassCurve.map_b₂]
end Formalism.L2.Th1.A
