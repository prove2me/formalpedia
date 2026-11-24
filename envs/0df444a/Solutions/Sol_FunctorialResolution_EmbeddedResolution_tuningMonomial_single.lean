-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:51:25.266225+00:00
-- url     : https://prove2.me/submissions/b17f386f-d89b-4fea-a9d5-0a8e6f1be4bc

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
theorem _root_.solution (J : Ideal S) (m i : ℕ) (hi : i ∈ Finset.range m) :
    tuningMonomial k J m (Pi.single i 1) = derivIdealIterate k i J := by
  rw [tuningMonomial_eq_prod, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro hni
    exact absurd hi hni
end FunctorialResolution.EmbeddedResolution
