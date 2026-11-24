-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_le_derivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:45.402105+00:00
-- url     : https://prove2.me/submissions/8cac1fef-031b-4c41-a2b8-b74b4dc60033

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    {I J : Ideal S} (h : I ≤ J) : derivIdeal k I ≤ derivIdeal k J :=
  derivIdeal_mono k h
end FunctorialResolution.EmbeddedResolution
