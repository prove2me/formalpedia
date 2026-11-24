-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tunedIdeal_antitone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:16:20.72879+00:00
-- url     : https://prove2.me/submissions/c7542380-9fbf-4605-98fe-145cf9b23f38

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningMonomial_le_tunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_le_iff

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
theorem _root_.solution (J : Ideal S) (m : ℕ) {s t : ℕ} (h : s ≤ t) :
    tunedIdeal k J m t ≤ tunedIdeal k J m s := by
  rw [tunedIdeal_le_iff]
  intro c hc
  exact tuningMonomial_le_tunedIdeal k J m s c (le_trans h hc)
end FunctorialResolution.EmbeddedResolution
