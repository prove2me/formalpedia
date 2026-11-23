-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.qd_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:01:46.044492+00:00
-- url     : https://prove2.me/submissions/4a64bb20-ce74-4ba3-b0f5-5b09c49c3d69

import Definitions.Def_Formalism_EllipticTorsion_IsoExpand
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_IsogenyExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.ELL Formalism.ELL.QuadraticDifferenceHypotheses
universe u
variable {O M Q : Type u} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup Q]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution (ψ : M → Q) (a b : M) : quadDiff ψ a b = quadDiff ψ b a := by
  unfold quadDiff; rw [add_comm]; abel
end Formalism.ELL.QuadraticDifferenceHypotheses
