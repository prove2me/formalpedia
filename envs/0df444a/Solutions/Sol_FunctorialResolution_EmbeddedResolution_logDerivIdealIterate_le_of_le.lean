-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.logDerivIdealIterate_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:55.530927+00:00
-- url     : https://prove2.me/submissions/f2a84c45-9ed3-4fba-8d8e-9cdced548e3f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LogDerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_logDerivIdealIterate_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_logDerivIdealIterate

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
theorem _root_.solution (P : Ideal S) {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    logDerivIdealIterate k P r J ≤ logDerivIdealIterate k P r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, logDerivIdealIterate_add]
  exact le_logDerivIdealIterate k P d _
end FunctorialResolution.EmbeddedResolution
