-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealIterate_tunedIdeal_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:21:26.946487+00:00
-- url     : https://prove2.me/submissions/c867b282-8dcd-4bbb-93b2-abd8ae9da1cb

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_pow_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_pow_eq_tunedIdeal_mul
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_tunedIdeal_le


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
theorem _root_.solution (J : Ideal S) (m L : ℕ) (hL : 0 < L)
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r : ℕ) (hr : m - 1 ≤ r) (i : ℕ) (hi : i < r * L) :
    derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L) ≤
      tunedIdeal k J m (r * L) ^ (r * L - i) := by
  have hi' : 1 ≤ r * L - i := Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hi)
  calc derivIdealIterate k i (tunedIdeal k J m (r * L)) ^ (r * L)
      ≤ tunedIdeal k J m (r * L - i) ^ (r * L) :=
        Ideal.pow_right_mono (derivIdealIterate_tunedIdeal_le k J m (r * L) i) (r * L)
    _ ≤ tunedIdeal k J m (r * L * (r * L - i)) := tunedIdeal_pow_le k J m (r * L - i) (r * L)
    _ = tunedIdeal k J m ((r * L - i) * (r * L)) := by
        rw [Nat.mul_comm (r * L) (r * L - i)]
    _ = tunedIdeal k J m (r * L) ^ (r * L - i) :=
        (tunedIdeal_pow_eq_tunedIdeal_mul k J m L hL hdvd r hr (r * L - i) hi').symm
end FunctorialResolution.EmbeddedResolution
