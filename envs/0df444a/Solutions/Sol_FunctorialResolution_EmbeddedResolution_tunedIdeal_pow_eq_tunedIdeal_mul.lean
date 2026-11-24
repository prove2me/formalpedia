-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_pow_eq_tunedIdeal_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:47.03935+00:00
-- url     : https://prove2.me/submissions/13b20b25-a54f-4609-a1a6-b8e7db892c6a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_mul_eq_tunedIdeal_add

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
    (hdvd : ∀ w : ℕ, 1 ≤ w → w ≤ m → w ∣ L) (r : ℕ) (hr : m - 1 ≤ r) (j : ℕ) (hj : 1 ≤ j) :
    tunedIdeal k J m (r * L) ^ j = tunedIdeal k J m (j * (r * L)) := by
  induction j with
  | zero => exact absurd hj (by omega)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        simp
      · have hn1 : 1 ≤ n := hn
        have ihn := ih hn1
        have hmt : (m - 1) * L ≤ n * (r * L) := by
          calc (m - 1) * L ≤ r * L := Nat.mul_le_mul hr (le_refl L)
            _ = 1 * (r * L) := (one_mul _).symm
            _ ≤ n * (r * L) := Nat.mul_le_mul hn1 (le_refl (r * L))
        calc tunedIdeal k J m (r * L) ^ (n + 1)
            = tunedIdeal k J m (r * L) ^ n * tunedIdeal k J m (r * L) := pow_succ _ _
          _ = tunedIdeal k J m (n * (r * L)) * tunedIdeal k J m (r * L) := by rw [ihn]
          _ = tunedIdeal k J m (r * L) * tunedIdeal k J m (n * (r * L)) := mul_comm _ _
          _ = tunedIdeal k J m (r * L + n * (r * L)) :=
              tunedIdeal_mul_eq_tunedIdeal_add k J m L hL hdvd r (n * (r * L)) hmt
          _ = tunedIdeal k J m ((n + 1) * (r * L)) := by
              rw [(by ring : r * L + n * (r * L) = (n + 1) * (r * L))]
end FunctorialResolution.EmbeddedResolution
