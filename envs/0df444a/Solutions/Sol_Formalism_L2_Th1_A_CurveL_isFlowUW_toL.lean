-- Prove2me | solution 1 for Formalism.L2.Th1.A.CurveL.isFlowUW_toL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:18.011184+00:00
-- url     : https://prove2.me/submissions/89dfec4b-4e75-4b51-bea6-27ac8831932c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_DL_toL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_fwAt_toL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_fuAt_toL
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_D_apply
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_deriv_wSer_mul_fw
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
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
open Formalism.L2.Th1.A.CurveL
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
namespace Formalism.L2.Th1.A.CurveL
theorem _root_.solution : IsFlowUW (curveL W) (DL W) (toL X) (toL (wSer W)) := by
  unfold IsFlowUW
  refine ⟨?_, ?_, ?_⟩
  · unfold WEq
    conv_lhs => rw [(CurveSer.wSer_fixed W).2]
    simp
  · rw [DL_toL, CurveSer.D_apply, derivative_X, mul_one, fwAt_toL]
  · rw [DL_toL, CurveSer.D_apply, mul_comm (fw W), CurveSer.deriv_wSer_mul_fw, fuAt_toL]
end Formalism.L2.Th1.A.CurveL
