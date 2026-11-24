-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.TaylorExpansion.truncatedSeries_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:30.687746+00:00
-- url     : https://prove2.me/submissions/087037ac-68b1-47de-9043-e3dee40d650c

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
theorem _root_.solution (σ : R →+* S) (D : Derivation A R R) (β : S) (N : ℕ) (hN : 1 ≤ N) :
    truncatedSeries σ D β N 1 = 1 := by
  have h1 : D (1 : R) = 0 := by simp
  rw [truncatedSeries_of_deriv_eq_zero σ D β N hN 1 h1, map_one]
end FunctorialResolution.EmbeddedResolution.TaylorExpansion
