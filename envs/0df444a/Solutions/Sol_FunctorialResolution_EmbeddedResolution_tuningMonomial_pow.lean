-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:05:21.846218+00:00
-- url     : https://prove2.me/submissions/123c5dfe-c01c-494e-8978-759e7cd37887

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_pow_fun_mul

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
theorem _root_.solution (J : Ideal S) (m n : ℕ) (c : ℕ → ℕ) :
    tuningMonomial k J m c ^ n = tuningMonomial k J m (n • c) := by
  have h : (n • c) = fun j => n * c j := by
    funext j
    simp [Pi.smul_apply, smul_eq_mul]
  rw [h, tuningMonomial_pow_fun_mul]
end FunctorialResolution.EmbeddedResolution
