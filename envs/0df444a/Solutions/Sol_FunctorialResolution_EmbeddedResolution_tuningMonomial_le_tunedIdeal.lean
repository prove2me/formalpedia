-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningMonomial_le_tunedIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:24.130634+00:00
-- url     : https://prove2.me/submissions/e494af80-9ef4-4540-8458-c1f2d7665819

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal

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
theorem _root_.solution (J : Ideal S) (m s : ℕ) (c : ℕ → ℕ)
    (hc : s ≤ tuningWeight m c) : tuningMonomial k J m c ≤ tunedIdeal k J m s :=
  le_iSup_of_le c (le_iSup_of_le hc le_rfl)
end FunctorialResolution.EmbeddedResolution
