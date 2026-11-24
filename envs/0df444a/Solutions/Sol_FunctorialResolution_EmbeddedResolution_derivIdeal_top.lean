-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdeal_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:47:31.871433+00:00
-- url     : https://prove2.me/submissions/d24a6175-4c62-4741-ab8e-56672397b7a2

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S] :
    derivIdeal k (⊤ : Ideal S) = ⊤ :=
  eq_top_iff.mpr (le_derivIdeal k ⊤)
end FunctorialResolution.EmbeddedResolution
