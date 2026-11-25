-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q2.nneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:55:24.273293+00:00
-- url     : https://prove2.me/submissions/055c0f7c-ae9f-4e57-b093-69494f96f36b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo

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
open Formalism.L2.Th1.A.Q2
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.A.Q2
theorem _root_.solution {a : K} (ha : ‖a‖ ≤ 1) : ‖-a‖ ≤ 1 := by
  rw [norm_neg]
  exact ha
end Formalism.L2.Th1.A.Q2
