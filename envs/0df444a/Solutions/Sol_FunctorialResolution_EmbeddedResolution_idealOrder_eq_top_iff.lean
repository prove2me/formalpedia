-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_eq_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:05:01.194057+00:00
-- url     : https://prove2.me/submissions/44ba7d71-6c08-45ed-b9fb-b1d65fb7c722

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
    idealOrder I = ⊤ ↔ ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n := by
  constructor
  · intro h n
    rw [← le_idealOrder_iff, h]
    exact le_top
  · intro h
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (le_idealOrder_iff I n).mpr (h n)
end FunctorialResolution.EmbeddedResolution
