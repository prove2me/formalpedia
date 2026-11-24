-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeriesRingHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:36.115609+00:00
-- url     : https://prove2.me/submissions/6497f443-9534-4da0-9222-c00118cbf3d0

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_TaylorExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution FunctorialResolution.EmbeddedResolution.TaylorExpansion
variable {A R S : Type*} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra ℚ S]
namespace FunctorialResolution.EmbeddedResolution.TaylorExpansion
theorem _root_.solution (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (J : Ideal S)
    (hN : 1 ≤ N) (hβ : β ^ N ∈ J) (f : R) :
    truncatedSeriesRingHom σ D β N J hN hβ f = Ideal.Quotient.mk J (truncatedSeries σ D β N f) :=
  rfl
end FunctorialResolution.EmbeddedResolution.TaylorExpansion
