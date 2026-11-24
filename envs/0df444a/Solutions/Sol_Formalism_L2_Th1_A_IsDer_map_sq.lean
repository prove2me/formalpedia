-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.map_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:20:19.156493+00:00
-- url     : https://prove2.me/submissions/ae0ef9c2-af17-4303-8767-d5e2ee655dff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowBasic
import Theorems.Thm_Formalism_L2_Th1_A_IsDer_map_mul

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
open Formalism.L2.Th1.A.IsDer
variable {A : Type u} [CommRing A] {D : A → A}
namespace Formalism.L2.Th1.A.IsDer
theorem _root_.solution (h : IsDer D) (a : A) : D (a ^ 2) = 2 * a * D a := by
  rw [pow_two, h.map_mul]
  ring
end Formalism.L2.Th1.A.IsDer
