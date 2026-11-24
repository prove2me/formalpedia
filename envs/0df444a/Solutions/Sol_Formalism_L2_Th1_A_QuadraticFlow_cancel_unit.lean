-- Prove2me | solution 1 for Formalism.L2.Th1.A.QuadraticFlow.cancel_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:14.88731+00:00
-- url     : https://prove2.me/submissions/59327cac-a6d7-404f-9c2d-4ab04754290b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo

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
theorem _root_.solution {k a b : A} (hk : IsUnit k) (e : k * a = k * b) : a = b := hk.mul_left_cancel e
end Formalism.L2.Th1.A.QuadraticFlow
