-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:30.373733+00:00
-- url     : https://prove2.me/submissions/4cf9e6f1-0f44-4d35-8aa5-33c05c641600

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {I J : Ideal R} (h : I ≤ J) : idealOrder J ≤ idealOrder I := by
  have hI : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  have hJ : idealOrder J
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | J ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  rw [hI, hJ]
  apply sSup_le
  rintro x ⟨n, hn, rfl⟩
  have hn' : I ≤ IsLocalRing.maximalIdeal R ^ n := le_trans h hn
  exact le_sSup ⟨n, hn', rfl⟩
end FunctorialResolution.EmbeddedResolution
