-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.weierstrassSubstitution_unit_fact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:25.148899+00:00
-- url     : https://prove2.me/submissions/a589e1d3-cd33-4e8c-83aa-00afa869aeb6

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Theorems.Thm_Formalism_L2_Th1_A_QuadraticFlow_unit_twelve

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.QuadraticFlow
variable {A : Type u} [CommRing A] {D : A → A}
namespace Formalism.L2.Th1.A.QuadraticFlow
theorem _root_.solution (h6 : IsUnit (6 : A)) : IsUnit (432 : A) := by
  have e : (432 : A) = 6 * 6 * 12 := by norm_num
  rw [e]
  exact (h6.mul h6).mul (unit_twelve h6)
end Formalism.L2.Th1.A.QuadraticFlow
