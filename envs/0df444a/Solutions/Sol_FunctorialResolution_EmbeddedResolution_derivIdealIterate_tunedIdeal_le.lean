-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealIterate_tunedIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:20:20.984416+00:00
-- url     : https://prove2.me/submissions/1554d3f2-51fa-496c-93a9-9a8076ea4f13

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tunedIdeal_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_tunedIdeal_succ_le
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_succ
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdealIterate_zero
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono


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
theorem _root_.solution (J : Ideal S) (m s j : ℕ) :
    derivIdealIterate k j (tunedIdeal k J m s) ≤ tunedIdeal k J m (s - j) := by
  induction j with
  | zero =>
      simp only [derivIdealIterate_zero, Nat.sub_zero]
      exact le_rfl
  | succ j ih =>
      rw [derivIdealIterate_succ]
      refine le_trans (derivIdeal_mono k ih) ?_
      rcases Nat.eq_zero_or_pos (s - j) with h | h
      · have hsj : s - (j + 1) = 0 := by omega
        rw [hsj, tunedIdeal_zero]
        exact le_top
      · obtain ⟨t, ht⟩ : ∃ t, s - j = t + 1 := ⟨s - j - 1, by omega⟩
        have hsj : s - (j + 1) = t := by omega
        rw [ht, hsj]
        exact derivIdeal_tunedIdeal_succ_le k J m t
end FunctorialResolution.EmbeddedResolution
