-- Prove2me | solution 1 for Formalism.L2.Th1.A.Plus.tS_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:05:25.72302+00:00
-- url     : https://prove2.me/submissions/e1e8254b-41ce-41c6-bdb3-96327fd8a46b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementP
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_ToLTDenMulInv
import Theorems.Thm_Formalism_L2_Th1_A_Plus_inv_subst
import Theorems.Thm_Formalism_ELL_wSeriesUnique
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
theorem _root_.solution (hI : ISerSpec.{u}) : (tS W xP).subst (iSer W) = tS W xP := by
  obtain ⟨hs0, -, -, -, -, -, -, -⟩ := hI R W
  have hS : HasSubst (iSer W) := HasSubst.of_constantCoeff_zero' hs0
  have hw0 : constantCoeff (wSer W) = 0 := (Formalism.ELL.wSeriesUnique R W).choose_spec.1.1
  have hB : iDen W * invOfUnit (iDen W) (-1) = 1 :=
    PowerSeries.mul_invOfUnit _ _ (by simp [iDen, hw0])
  rw [tS, ← PowerSeries.coe_substAlgHom hS, map_mul, map_pow, PowerSeries.coe_substAlgHom,
    PowerSeries.subst_X hS, inv_subst W xP hI, iSer]
  linear_combination (X ^ 2 * invOfUnit (tDen W xP) 1 * (iDen W * invOfUnit (iDen W) (-1) + 1)) * hB
end Formalism.L2.Th1.A.Plus
