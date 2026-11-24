-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealIterate_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:47:42.658801+00:00
-- url     : https://prove2.me/submissions/03ee8744-7a64-42fe-98f6-3673c7cf6dfe

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal

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
    (J : Ideal S) : derivIdealIterate k 1 J = derivIdeal k J := rfl
end FunctorialResolution.EmbeddedResolution
