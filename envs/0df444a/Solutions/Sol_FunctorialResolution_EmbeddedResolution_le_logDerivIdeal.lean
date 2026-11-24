-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_logDerivIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:25.432585+00:00
-- url     : https://prove2.me/submissions/cd0b1fbd-d4d9-461f-9cd8-47d561f8fcdb

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
section
namespace FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
private theorem logDerivIdeal_eq_sup_span (P J : Ideal S) :
    logDerivIdeal k P J =
      J ⊔ Ideal.span {x : S | ∃ D ∈ tangentDerivations k P, ∃ y ∈ J, D y = x} := rfl
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
variable (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (P J : Ideal S) : J ≤ logDerivIdeal k P J := by
  rw [logDerivIdeal_eq_sup_span]
  exact le_sup_left
end FunctorialResolution.EmbeddedResolution
