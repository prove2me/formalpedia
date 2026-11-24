-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:32.019039+00:00
-- url     : https://prove2.me/submissions/d1817da0-d95d-49b9-b649-8e6786a3d167

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_mul_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_zero


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
theorem _root_.solution (J : Ideal S) (m a n : ℕ) :
    tunedIdeal k J m a ^ n ≤ tunedIdeal k J m (n * a) := by
  induction n with
  | zero => simp [tunedIdeal_zero]
  | succ n ih =>
      calc tunedIdeal k J m a ^ (n + 1)
          = tunedIdeal k J m a ^ n * tunedIdeal k J m a := pow_succ _ _
        _ ≤ tunedIdeal k J m (n * a) * tunedIdeal k J m a := Ideal.mul_mono ih le_rfl
        _ ≤ tunedIdeal k J m (n * a + a) := tunedIdeal_mul_le k J m _ _
        _ = tunedIdeal k J m ((n + 1) * a) := by
            rw [(by ring : n * a + a = (n + 1) * a)]
end FunctorialResolution.EmbeddedResolution
