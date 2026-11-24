-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:30.168407+00:00
-- url     : https://prove2.me/submissions/922f0a1a-39c3-4732-941d-cb06fccc6b23

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_eq_top_iff

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
theorem _root_.solution : idealOrder (⊥ : Ideal R) = ⊤ := by
  rw [idealOrder_eq_top_iff]
  intro n
  exact bot_le
end FunctorialResolution.EmbeddedResolution
