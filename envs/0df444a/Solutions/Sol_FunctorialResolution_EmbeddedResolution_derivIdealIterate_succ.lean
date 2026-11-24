-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealIterate_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:43.78788+00:00
-- url     : https://prove2.me/submissions/9d9af6ae-0225-4966-9513-58e2d9a5ff92

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
    (r : ℕ) (J : Ideal S) :
    derivIdealIterate k (r + 1) J = derivIdeal k (derivIdealIterate k r J) := rfl
end FunctorialResolution.EmbeddedResolution
