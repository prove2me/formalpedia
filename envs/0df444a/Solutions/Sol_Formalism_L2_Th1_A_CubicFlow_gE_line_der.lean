-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubicFlow.gE_line_der
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:25.400062+00:00
-- url     : https://prove2.me/submissions/b1349cee-5c57-4dc2-a62a-5027c94f7ded

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTwo
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowThird

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
open Formalism.L2.Th1.A.CubicFlow
open QuadraticFlow
variable {A : Type u} [CommRing A]
namespace Formalism.L2.Th1.A.CubicFlow
theorem _root_.solution (W : WeierstrassCurve A) (l n z : A) :
    fuAt W z (l * z + n) - l * fwAt W z (l * z + n)
      = 3 * k3 W l * z ^ 2 + 2 * k2 W l n * z + k1 W l n := by
  unfold fuAt fwAt k3 k2 k1
  ring
end Formalism.L2.Th1.A.CubicFlow
