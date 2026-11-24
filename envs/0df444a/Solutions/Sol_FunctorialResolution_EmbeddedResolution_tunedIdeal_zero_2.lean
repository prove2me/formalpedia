-- Prove2me | solution 2 for FunctorialResolution.EmbeddedResolution.tunedIdeal_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:05:29.664056+00:00
-- url     : https://prove2.me/submissions/d91a1cea-711e-4ffe-95db-0b1bb990bad2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal

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
theorem _root_.solution (J : Ideal S) (m : ℕ) : tunedIdeal k J m 0 = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← tuningMonomial_zero k J m]
  exact tuningMonomial_le_tunedIdeal k J m 0 (fun _ => 0) (Nat.zero_le _)
end FunctorialResolution.EmbeddedResolution
