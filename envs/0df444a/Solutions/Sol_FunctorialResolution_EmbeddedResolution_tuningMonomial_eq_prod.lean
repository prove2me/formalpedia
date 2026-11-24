-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:29.589804+00:00
-- url     : https://prove2.me/submissions/28c95fc9-e57c-4e79-a53c-a085e7094ce2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal

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
theorem _root_.solution (J : Ideal S) (m : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c = ∏ j ∈ Finset.range m, derivIdealIterate k j J ^ c j := rfl
end FunctorialResolution.EmbeddedResolution
