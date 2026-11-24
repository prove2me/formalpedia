-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.span_pow_mul_tunedIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:38:17.462002+00:00
-- url     : https://prove2.me/submissions/60dce8d7-1a57-41da-b4e3-e56025da35b4

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_antitone
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_mul_tunedIdeal_le_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_span_pow_mul_tuningMonomial_le

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
theorem _root_.solution (J : Ideal S) (m : ℕ) (hm : 1 ≤ m) {x : S}
    (hx : x ∈ derivIdealIterate k (m - 1) J) (n t : ℕ) :
    Ideal.span {x ^ n} * tunedIdeal k J m t ≤ tunedIdeal k J m (t + n) := by
  rw [mul_tunedIdeal_le_iff]
  intro c hc
  refine le_trans (span_pow_mul_tuningMonomial_le k J m hm hx n c) ?_
  exact tunedIdeal_antitone k J m (Nat.add_le_add_right hc n)
end FunctorialResolution.EmbeddedResolution
