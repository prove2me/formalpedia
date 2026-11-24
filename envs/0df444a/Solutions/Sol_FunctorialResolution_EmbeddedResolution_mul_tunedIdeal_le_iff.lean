-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mul_tunedIdeal_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:13.34048+00:00
-- url     : https://prove2.me/submissions/f11d5482-e965-4a8b-af41-798133e4574f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_eq_iSup
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal

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
theorem _root_.solution (I J : Ideal S) (m s : ℕ) (K : Ideal S) :
    I * tunedIdeal k J m s ≤ K ↔
      ∀ c : ℕ → ℕ, s ≤ tuningWeight m c → I * tuningMonomial k J m c ≤ K := by
  constructor
  · intro h c hc
    exact le_trans (Ideal.mul_mono le_rfl (tuningMonomial_le_tunedIdeal k J m s c hc)) h
  · intro h
    rw [tunedIdeal_eq_iSup, Submodule.mul_iSup]
    refine iSup_le fun c => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun hc => h c hc
end FunctorialResolution.EmbeddedResolution
