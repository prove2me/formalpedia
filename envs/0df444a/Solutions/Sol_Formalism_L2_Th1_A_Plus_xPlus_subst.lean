-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.xPlus_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:11.810788+00:00
-- url     : https://prove2.me/submissions/f353d9e3-def8-4657-9527-0eff981234a1

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_inv_subst
import Theorems.Thm_Formalism_L2_Th1_A_Plus_nS_subst
import Theorems.Thm_Formalism_ELL_wSeriesUnique
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_pow
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
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Plus
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)
namespace Formalism.L2.Th1.A.Plus
theorem _root_.solution (hI : ISerSpec.{u}) :
    (xPlus W xP yP).subst (iSer W) = xPlus W xP (W.toAffine.negY xP yP) := by
  obtain ⟨hs0, -, -, -, -, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  have hCs : (C xP : R⟦X⟧).subst (iSer W) = C xP := by
    rw [← PowerSeries.coe_substAlgHom hS]
    exact (PowerSeries.substAlgHom hS).commutes xP
  rw [xPlus, xPlus, ← PowerSeries.coe_substAlgHom hS, map_add, map_mul, map_mul, map_pow,
    PowerSeries.coe_substAlgHom, PowerSeries.subst_X hS, hCs, nS_subst W xP yP hI, inv_subst W xP hI, iSer]
  linear_combination (X * nS W xP (W.toAffine.negY xP yP) * invOfUnit (tDen W xP) 1 ^ 2 * (iDen W * invOfUnit (iDen W) (-1) + 1) * ((iDen W * invOfUnit (iDen W) (-1)) ^ 2 + 1)) * hB
end Formalism.L2.Th1.A.Plus
