-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_derivIdealIterate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:49:13.963925+00:00
-- url     : https://prove2.me/submissions/53d28864-df99-424d-83ba-aebbb6a1fca7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ

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
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S] [Algebra k S]
    (r : ℕ) (J : Ideal S) : J ≤ derivIdealIterate k r J := by
  induction r with
  | zero => exact (derivIdealIterate_zero k J).ge
  | succ r ih =>
      rw [derivIdealIterate_succ]
      exact ih.trans (le_derivIdeal k _)
end FunctorialResolution.EmbeddedResolution
