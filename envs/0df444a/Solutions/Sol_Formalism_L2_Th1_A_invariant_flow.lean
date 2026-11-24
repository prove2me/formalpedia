-- Prove2me | solution 1 for Formalism.L2.Th1.A.invariant_flow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:45.169708+00:00
-- url     : https://prove2.me/submissions/89305844-2a78-4285-95c3-f631279dfdd8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_isFlow_xL_yL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_toL_X_mul_yL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_toL_wSer_mul_yL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_toL_wSer_mul_xL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open CurveL
namespace Formalism.L2.Th1.A
theorem _root_.solution : FlowL.{u} := by
  unfold FlowL
  intro R _ W
  exact ⟨isFlow_xL_yL W, toL_X_mul_yL W, toL_wSer_mul_yL W, toL_wSer_mul_xL W⟩
end Formalism.L2.Th1.A
