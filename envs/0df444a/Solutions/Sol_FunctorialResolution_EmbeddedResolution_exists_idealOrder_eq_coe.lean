-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.exists_idealOrder_eq_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:40.792357+00:00
-- url     : https://prove2.me/submissions/07d8e0e9-88c4-4991-a1a2-6ab38a85ac9b

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_ne_top_of_ne_bot

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
theorem _root_.solution [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    ∃ n : ℕ, idealOrder I = (n : ℕ∞) := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (idealOrder_ne_top_of_ne_bot hI)
  exact ⟨n, hn.symm⟩
end FunctorialResolution.EmbeddedResolution
