-- Prove2me | solution 1 for Formalism.L2.Th1.A.Q2.nsub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:11:53.824694+00:00
-- url     : https://prove2.me/submissions/81a24c04-900b-43f4-a131-08f4021432f8

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementQ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowDouble
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_NormLeOneOfMonicTwo
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nadd
import Theorems.Thm_Formalism_L2_Th1_A_Q2_nneg
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
theorem _root_.solution {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact nadd ha (nneg hb)
end Formalism.L2.Th1.A.Q2
