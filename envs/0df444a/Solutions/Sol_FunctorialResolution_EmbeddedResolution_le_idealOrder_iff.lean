-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.le_idealOrder_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:44.625693+00:00
-- url     : https://prove2.me/submissions/d8c22428-e43c-4f0e-8387-14069eeb2629

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I : Ideal R) (n : ℕ) :
    (n : ℕ∞) ≤ idealOrder I ↔ I ≤ IsLocalRing.maximalIdeal R ^ n := by
  have hdef : idealOrder I
      = sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k}) := rfl
  constructor
  · intro h
    by_contra hI
    rw [hdef] at h
    have hn : n ≠ 0 := by
      rintro rfl
      apply hI
      rw [pow_zero, Ideal.one_eq_top]
      exact le_top
    have hsup : sSup ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | I ≤ IsLocalRing.maximalIdeal R ^ k})
        ≤ ((n - 1 : ℕ) : ℕ∞) := by
      apply sSup_le
      rintro x ⟨k, hk, rfl⟩
      have hk' : I ≤ IsLocalRing.maximalIdeal R ^ k := hk
      have hkn : k < n := by
        by_contra hkn
        push Not at hkn
        exact hI (le_trans hk' (Ideal.pow_le_pow_right hkn))
      have hk2 : k ≤ n - 1 := by omega
      show (k : ℕ∞) ≤ ((n - 1 : ℕ) : ℕ∞)
      exact_mod_cast hk2
    have hcon : n ≤ n - 1 := by exact_mod_cast h.trans hsup
    omega
  · intro h
    rw [hdef]
    exact le_sSup ⟨n, h, rfl⟩
end FunctorialResolution.EmbeddedResolution
