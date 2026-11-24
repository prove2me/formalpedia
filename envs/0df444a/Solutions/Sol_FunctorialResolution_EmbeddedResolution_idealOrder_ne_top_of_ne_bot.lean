-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.idealOrder_ne_top_of_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:50.196271+00:00
-- url     : https://prove2.me/submissions/6e036caf-1f61-4d2d-ae03-43961697fb61

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_eq_top_iff

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
theorem _root_.solution [IsNoetherianRing R] {I : Ideal R} (hI : I ≠ ⊥) :
    idealOrder I ≠ ⊤ := by
  intro h
  rw [idealOrder_eq_top_iff] at h
  have key : (⨅ n : ℕ, IsLocalRing.maximalIdeal R ^ n) = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing (I := IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hle : I ≤ ⊥ := by
    rw [← key]
    exact le_iInf h
  exact hI (le_bot_iff.mp hle)
end FunctorialResolution.EmbeddedResolution
