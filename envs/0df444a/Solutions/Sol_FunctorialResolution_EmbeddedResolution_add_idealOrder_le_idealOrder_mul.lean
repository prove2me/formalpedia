-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.add_idealOrder_le_idealOrder_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:31.563791+00:00
-- url     : https://prove2.me/submissions/147cbd1f-9fb4-4c29-ad92-141cbe7a8d67

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_le_idealOrder_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
private theorem enat_add_le_of_forall_natCast_add_le {a b c : ℕ∞}
    (h : ∀ m n : ℕ, (m : ℕ∞) ≤ a → (n : ℕ∞) ≤ b → ((m + n : ℕ) : ℕ∞) ≤ c) : a + b ≤ c := by
  rcases eq_or_ne a ⊤ with rfl | ha
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h n 0 le_top (by simp)
      simpa using hn
    rw [hc]
    exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · have hc : c = ⊤ := by
      rw [ENat.eq_top_iff_forall_ge]
      intro n
      have hn := h 0 n (by simp) le_top
      simpa using hn
    rw [hc]
    exact le_top
  lift a to ℕ using ha
  lift b to ℕ using hb
  have hab := h a b le_rfl le_rfl
  simpa using hab
end FunctorialResolution.EmbeddedResolution
end

set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
variable {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (I J : Ideal R) :
    idealOrder I + idealOrder J ≤ idealOrder (I * J) := by
  refine enat_add_le_of_forall_natCast_add_le (fun m n hm hn => ?_)
  rw [le_idealOrder_iff] at hm hn ⊢
  rw [pow_add]
  exact Ideal.mul_mono hm hn
end FunctorialResolution.EmbeddedResolution
