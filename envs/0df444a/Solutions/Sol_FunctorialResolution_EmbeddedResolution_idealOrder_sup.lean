-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_sup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:12.016837+00:00
-- url     : https://prove2.me/submissions/9fa8f4e4-dd49-4499-84a9-eaaa4953c9e2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_le_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I J : Ideal R) :
    idealOrder (I ⊔ J) = min (idealOrder I) (idealOrder J) := by
  apply le_antisymm
  · exact le_min (idealOrder_le_of_le (le_sup_left : I ≤ I ⊔ J))
      (idealOrder_le_of_le (le_sup_right : J ≤ I ⊔ J))
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    rw [le_min_iff] at hn
    rw [le_idealOrder_iff]
    exact sup_le ((le_idealOrder_iff I n).mp hn.1) ((le_idealOrder_iff J n).mp hn.2)
end FunctorialResolution.EmbeddedResolution
