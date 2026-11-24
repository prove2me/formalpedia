-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:22.162166+00:00
-- url     : https://prove2.me/submissions/23b3dc96-5d5d-403d-8940-86c69c7676b4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_mul_fun_add

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
theorem _root_.solution (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (c + d) :=
  tuningMonomial_mul_fun_add k J m c d
end FunctorialResolution.EmbeddedResolution
