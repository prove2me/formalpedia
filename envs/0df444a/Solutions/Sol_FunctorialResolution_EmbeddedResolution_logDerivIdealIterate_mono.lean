-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealIterate_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:11.441224+00:00
-- url     : https://prove2.me/submissions/ed3e1ec3-ca54-4a10-bfdb-4a23e95a62de

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_succ

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
theorem _root_.solution (P : Ideal S) (r : ℕ) :
    Monotone (logDerivIdealIterate k P r : Ideal S → Ideal S) := by
  induction r with
  | zero =>
      intro I J h
      rw [logDerivIdealIterate_zero, logDerivIdealIterate_zero]
      exact h
  | succ r ih =>
      intro I J h
      rw [logDerivIdealIterate_succ, logDerivIdealIterate_succ]
      exact logDerivIdeal_mono k P (ih h)
end FunctorialResolution.EmbeddedResolution
