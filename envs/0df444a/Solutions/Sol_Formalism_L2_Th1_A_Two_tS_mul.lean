-- Prove2me | solution 1 for Formalism.L2.Th1.A.Two.tS_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:42:43.500565+00:00
-- url     : https://prove2.me/submissions/2a86c51c-94b5-4547-a0aa-ded7cd97a6af

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementI
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_TwoTorsionIntegral
import Theorems.Thm_Formalism_L2_Th1_A_Two_toL_exp_ne
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_one
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_sub
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_toDerivation_apply
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
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Two
variable {K : Type u} [Field K] [CharZero K] (W : WeierstrassCurve K)
namespace Formalism.L2.Th1.A.Two
theorem _root_.solution (xP : K) :
    toL ((tS W xP).subst (expSer W)) * (xZ W - HahnSeries.C xP) = 1 := by
  have hne := toL_exp_ne W
  have hc : constantCoeff (tDen W xP) = 1 := by
    simp [tDen, xS, PowerSeries.constantCoeff_invOfUnit]
  have hm : tDen W xP * invOfUnit (tDen W xP) 1 = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simpa using hc)
  have hC : (C xP : K⟦X⟧).subst (expSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom (he W)]
    exact (PowerSeries.substAlgHom (he W)).commutes xP
  have ht : (xS W).subst (expSer W) = (tDen W xP).subst (expSer W) + C xP * expSer W ^ 2 := by
    rw [tDen, ← PowerSeries.coe_substAlgHom (he W), map_sub, map_mul, map_pow,
      PowerSeries.coe_substAlgHom, PowerSeries.subst_X (he W), hC]
    ring
  have h1 : toL ((tDen W xP).subst (expSer W)) * toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) = 1 := by
    rw [← map_mul, ← PowerSeries.coe_substAlgHom (he W), ← map_mul, hm, map_one, map_one]
  have hE : toL (expSer W) * (toL (expSer W))⁻¹ = 1 := mul_inv_cancel₀ hne
  have hs : (tS W xP).subst (expSer W) = expSer W ^ 2 * (invOfUnit (tDen W xP) 1).subst (expSer W) := by
    rw [tS, ← PowerSeries.coe_substAlgHom (he W), map_mul, map_pow, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_X (he W)]
  rw [hs, xZ, ht]
  simp only [map_add, map_mul, map_pow, HahnSeries.ofPowerSeries_C]
  linear_combination (toL (expSer W) * (toL (expSer W))⁻¹ + 1) * (toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) * toL ((tDen W xP).subst (expSer W)) + HahnSeries.C xP * toL ((invOfUnit (tDen W xP) 1).subst (expSer W)) * toL (expSer W) ^ 2) * hE + h1
end Formalism.L2.Th1.A.Two
