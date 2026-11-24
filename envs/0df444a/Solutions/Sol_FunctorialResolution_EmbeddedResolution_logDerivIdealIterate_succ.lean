-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealIterate_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:24.041849+00:00
-- url     : https://prove2.me/submissions/e91d14f5-2226-42ac-ba7f-6b0210481228

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal

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
theorem _root_.solution (P : Ideal S) (r : ℕ) (J : Ideal S) :
    logDerivIdealIterate k P (r + 1) J = logDerivIdeal k P (logDerivIdealIterate k P r J) := rfl
end FunctorialResolution.EmbeddedResolution
