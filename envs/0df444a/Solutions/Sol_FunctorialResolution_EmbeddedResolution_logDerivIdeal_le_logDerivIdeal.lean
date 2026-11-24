-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdeal_le_logDerivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:06.70346+00:00
-- url     : https://prove2.me/submissions/e2578675-b6b1-4492-82c7-339c54af6928

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (P : Ideal S) {I J : Ideal S} (h : I ≤ J) :
    logDerivIdeal k P I ≤ logDerivIdeal k P J :=
  logDerivIdeal_mono k P h
end FunctorialResolution.EmbeddedResolution
