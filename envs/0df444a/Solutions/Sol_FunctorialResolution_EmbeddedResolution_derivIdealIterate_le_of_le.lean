-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealIterate_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:02:37.096314+00:00
-- url     : https://prove2.me/submissions/2b03e9f0-0fce-4219-bf90-ff4e60e5a2b3

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_add
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_derivIdealIterate

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
    {r r' : ℕ} (h : r ≤ r') (J : Ideal S) :
    derivIdealIterate k r J ≤ derivIdealIterate k r' J := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_comm r d, derivIdealIterate_add]
  exact le_derivIdealIterate k d _
end FunctorialResolution.EmbeddedResolution
