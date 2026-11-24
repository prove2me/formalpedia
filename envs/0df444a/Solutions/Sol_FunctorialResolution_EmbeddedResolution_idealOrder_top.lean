-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:38.220403+00:00
-- url     : https://prove2.me/submissions/c20728df-a929-4b9e-8bf6-cd75ce99bf6b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_one_le_idealOrder_iff_ne_top

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
theorem _root_.solution : idealOrder (⊤ : Ideal R) = 0 := by
  by_contra h
  have h1 : (1 : ℕ∞) ≤ idealOrder (⊤ : Ideal R) := by
    rw [Order.one_le_iff_ne_zero]
    exact h
  rw [one_le_idealOrder_iff_ne_top] at h1
  exact h1 rfl
end FunctorialResolution.EmbeddedResolution
