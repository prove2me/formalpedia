-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mul_idealOrder_le_idealOrder_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:50:12.660621+00:00
-- url     : https://prove2.me/submissions/a1fa9c12-42f1-4955-9a95-4a849bccd671

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_idealOrder_eq_top_iff

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
theorem _root_.solution (I : Ideal R) (c : ℕ) :
    (c : ℕ∞) * idealOrder I ≤ idealOrder (I ^ c) := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · rw [Nat.cast_zero, zero_mul]
    exact zero_le
  · have hc1 : 1 ≤ c := hc
    rcases eq_or_ne (idealOrder I) ⊤ with hI | hI
    · have hIall : ∀ n : ℕ, I ≤ IsLocalRing.maximalIdeal R ^ n :=
        (idealOrder_eq_top_iff I).mp hI
      have htop : idealOrder (I ^ c) = ⊤ := by
        rw [idealOrder_eq_top_iff]
        intro n
        have h1 : I ^ c ≤ I ^ 1 := Ideal.pow_le_pow_right hc1
        rw [pow_one] at h1
        exact le_trans h1 (hIall n)
      rw [htop]
      exact le_top
    · obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hI
      have hIk : I ≤ IsLocalRing.maximalIdeal R ^ k := (le_idealOrder_iff I k).mp hk.le
      rw [← hk, ← Nat.cast_mul, le_idealOrder_iff]
      calc I ^ c ≤ (IsLocalRing.maximalIdeal R ^ k) ^ c :=
            Ideal.pow_right_mono hIk c
        _ = IsLocalRing.maximalIdeal R ^ (c * k) := by rw [← pow_mul, mul_comm k c]
end FunctorialResolution.EmbeddedResolution
