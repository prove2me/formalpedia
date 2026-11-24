-- Prove2me | solution 1 for Formalism.L2.Th1.A.invariant_derivation_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:44:18.876958+00:00
-- url     : https://prove2.me/submissions/31258671-10ac-40eb-b135-d02dd40cfd20

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_Laurent
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveSer
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_CurveL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_isDer_DL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_DL_C
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_constCurve_DL
import Theorems.Thm_Formalism_L2_Th1_A_CurveL_DL_toL

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
theorem _root_.solution : DLSpec.{u} := by
  unfold DLSpec
  intro R _ W
  exact ⟨isDer_DL W, constCurve_DL W, DL_C W, DL_toL W⟩
end Formalism.L2.Th1.A
