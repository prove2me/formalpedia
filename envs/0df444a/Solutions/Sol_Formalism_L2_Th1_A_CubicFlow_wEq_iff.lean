-- Prove2me | solution 1 for Formalism.L2.Th1.A.CubicFlow.wEq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:19:26.533414+00:00
-- url     : https://prove2.me/submissions/08ee0249-8dc2-43ba-9a6c-c20e3d717034

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
theorem _root_.solution (W : WeierstrassCurve A) (z v : A) : WEq W z v ↔ gE W z v = 0 := by
  unfold WEq gE
  constructor <;> intro h <;> linear_combination -h
end Formalism.L2.Th1.A.CubicFlow
