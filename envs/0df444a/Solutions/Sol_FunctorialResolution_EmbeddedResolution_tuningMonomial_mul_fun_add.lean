-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_mul_fun_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:49.909795+00:00
-- url     : https://prove2.me/submissions/70e6fc49-5e98-4c4a-833c-ad83ddc0d835

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
theorem _root_.solution (J : Ideal S) (m : ℕ) (c d : ℕ → ℕ) :
    tuningMonomial k J m c * tuningMonomial k J m d = tuningMonomial k J m (fun j => c j + d j) := by
  rw [tuningMonomial_eq_prod, tuningMonomial_eq_prod, tuningMonomial_eq_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun j _ => (pow_add _ _ _).symm
end FunctorialResolution.EmbeddedResolution
