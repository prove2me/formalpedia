-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:26.893793+00:00
-- url     : https://prove2.me/submissions/0b314d09-5b39-46f6-b943-be83e20003f2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_eq_prod

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
theorem _root_.solution (J : Ideal S) (m : ℕ) :
    tuningMonomial k J m (fun _ => 0) = ⊤ := by
  simp [tuningMonomial_eq_prod, Ideal.one_eq_top]
end FunctorialResolution.EmbeddedResolution
