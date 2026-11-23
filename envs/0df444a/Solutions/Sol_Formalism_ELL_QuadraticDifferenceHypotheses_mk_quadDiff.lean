-- Prove2me | solution 1 for Formalism.ELL.QuadraticDifferenceHypotheses.mk_quadDiff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:00:05.56381+00:00
-- url     : https://prove2.me/submissions/5d59f21f-c33a-4391-b429-cf506c116edb

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
variable {O S M T : Type u} [CommRing O] [CommRing S] [AddCommGroup M] [Module O M]
    [AddCommGroup T] [Module S T]
namespace Formalism.ELL.QuadraticDifferenceHypotheses
theorem _root_.solution (N : AddSubgroup T) (φ : M → T) (a b : M) :
    QuotientAddGroup.mk' N (quadDiff φ a b) =
      quadDiff (fun a => QuotientAddGroup.mk' N (φ a)) a b := by
  simp [quadDiff, map_sub]
end Formalism.ELL.QuadraticDifferenceHypotheses
