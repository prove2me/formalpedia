-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.nS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:44:15.279669+00:00
-- url     : https://prove2.me/submissions/f381ebe3-84a5-4ea4-b8e1-2389844541c5

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_add
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_neg
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_ofNat
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
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Plus
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (xP yP : R)
namespace Formalism.L2.Th1.A.Plus
theorem _root_.solution (hI : ISerSpec.{u}) : (nS W xP yP).subst (iSer W)
    = invOfUnit (iDen W) (-1) ^ 3 * nS W xP (W.toAffine.negY xP yP) := by
  obtain ⟨hs0, -, -, -, hx, hy, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hCs : ∀ r : R, (C r : R⟦X⟧).subst (iSer W) = C r := fun r => by
    rw [← PowerSeries.coe_substAlgHom hS]
    exact (PowerSeries.substAlgHom hS).commutes r
  rw [nS, nS, ← PowerSeries.coe_substAlgHom hS]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg]
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_X hS, hCs, hx, hy]
  simp only [iSer, WeierstrassCurve.Affine.negY, map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat]
  ring
end Formalism.L2.Th1.A.Plus
