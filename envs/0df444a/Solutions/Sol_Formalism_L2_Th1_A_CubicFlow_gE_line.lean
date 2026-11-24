-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubicFlow.gE_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:24.355795+00:00
-- url     : https://prove2.me/submissions/24f0e083-8473-48c2-8467-af19d2d5f9f6

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
    gE W z (l * z + n) = k3 W l * z ^ 3 + k2 W l n * z ^ 2 + k1 W l n * z + k0 W n := by
  unfold gE k3 k2 k1 k0
  ring
end Formalism.L2.Th1.A.CubicFlow
