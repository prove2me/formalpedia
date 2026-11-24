-- Prove2me | solution 1 for Formalism.L2.Th1.A.unit_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:29:34.142821+00:00
-- url     : https://prove2.me/submissions/2b89cf14-fa84-48ac-834d-df2e8469701a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_wSer_fixed
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_D_apply
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_deriv_wSer_mul_fw
import Theorems.Thm_Formalism_L2_Th1_A_CurveSer_om_mul_D

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u v
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open CurveSer
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowU.{u} := by
  unfold FlowU
  intro R _ W
  have hfw : fwAt (curveS W) X (wSer W) = fw W := by
    unfold fwAt fw
    simp
  have hfu : fuAt (curveS W) X (wSer W) = fu W := by
    unfold fuAt fu
    simp
  refine ⟨?_, ?_, ?_, hfw, hfu, om_mul_D W⟩
  · unfold IsDer
    exact ⟨fun a b => map_add (D W) a b, fun a b => by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]⟩
  · unfold ConstCurve
    simp [D_apply]
  · unfold IsFlowUW
    refine ⟨?_, ?_, ?_⟩
    · unfold WEq
      simpa using (wSer_fixed W).2
    · rw [D_apply, derivative_X, mul_one, hfw]
    · rw [D_apply, mul_comm, deriv_wSer_mul_fw W, hfu]
end Formalism.L2.Th1.A
