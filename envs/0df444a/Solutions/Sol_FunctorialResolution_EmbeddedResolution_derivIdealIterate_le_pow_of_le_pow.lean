-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.derivIdealIterate_le_pow_of_le_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:25.238715+00:00
-- url     : https://prove2.me/submissions/cb54a201-ccc4-422d-841f-167f9635e99a

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_mono
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_derivIdeal_pow_le
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
theorem _root_.solution (k : Type*) [CommRing k] {S : Type*} [CommRing S]
    [Algebra k S] {I P : Ideal S} {n : ℕ} (r : ℕ) (h : I ≤ P ^ n) :
    derivIdealIterate k r I ≤ P ^ (n - r) := by
  induction r with
  | zero =>
      rw [derivIdealIterate_zero, Nat.sub_zero]
      exact h
  | succ r ih =>
      rw [derivIdealIterate_succ]
      have h1 : derivIdeal k (derivIdealIterate k r I) ≤ derivIdeal k (P ^ (n - r)) :=
        derivIdeal_mono k ih
      have h2 : derivIdeal k (P ^ (n - r)) ≤ P ^ (n - r - 1) := derivIdeal_pow_le k P (n - r)
      have h3 : n - r - 1 = n - (r + 1) := by omega
      rw [h3] at h2
      exact h1.trans h2
end FunctorialResolution.EmbeddedResolution
