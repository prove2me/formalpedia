-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.one_le_idealOrder_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:01.293852+00:00
-- url     : https://prove2.me/submissions/815e5dec-3ce7-418f-9a1a-4b7fe2686d95

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff

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
    1 ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R := by
  have h := le_idealOrder_iff I 1
  rw [Nat.cast_one, pow_one] at h
  exact h
end FunctorialResolution.EmbeddedResolution
