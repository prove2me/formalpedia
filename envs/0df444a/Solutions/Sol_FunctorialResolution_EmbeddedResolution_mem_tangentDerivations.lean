-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_tangentDerivations
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:29.082849+00:00
-- url     : https://prove2.me/submissions/fa49e9c0-dd9e-411c-b102-7dd8f4db686f

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
theorem _root_.solution (P : Ideal S) (D : Derivation k S S) :
    D ∈ tangentDerivations k P ↔ ∀ x ∈ P, D x ∈ P := Iff.rfl
end FunctorialResolution.EmbeddedResolution
