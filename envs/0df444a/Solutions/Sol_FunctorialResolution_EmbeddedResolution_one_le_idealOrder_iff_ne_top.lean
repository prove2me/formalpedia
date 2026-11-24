-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.one_le_idealOrder_iff_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:50:12.309424+00:00
-- url     : https://prove2.me/submissions/1dab9d25-e81e-4d6d-9014-b503d30dc3b7

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
    1 ≤ idealOrder I ↔ I ≠ ⊤ := by
  rw [one_le_idealOrder_iff]
  constructor
  · intro h hI
    rw [hI] at h
    exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp h)
  · intro h
    exact IsLocalRing.le_maximalIdeal h
end FunctorialResolution.EmbeddedResolution
