-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:49:11.130547+00:00
-- url     : https://prove2.me/submissions/53d7ad3b-7361-4f7b-bd67-14d390962654

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_idealOrder_iff

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
theorem _root_.solution (I : Ideal R) :
    idealOrder I = 0 ↔ ¬ I ≤ IsLocalRing.maximalIdeal R := by
  rw [← one_le_idealOrder_iff, not_le, Order.lt_one_iff]
end FunctorialResolution.EmbeddedResolution
