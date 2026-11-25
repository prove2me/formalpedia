-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q2.nadd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:54:47.701811+00:00
-- url     : https://prove2.me/submissions/c1d3e46c-64b7-417e-8c52-2dcfc01d536c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
theorem _root_.solution {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
end Formalism.L2.Th1.A.Q2
