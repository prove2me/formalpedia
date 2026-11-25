-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:25:03.786947+00:00
-- url     : https://prove2.me/submissions/00027204-a68e-4aea-84b0-ed062a83128e

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_finite
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_card
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_finsum_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.DoubleCosetLemmas
variable {G M : Type} [Group G] [MeasurableSpace M]
variable {dx : Measure M} {φ : G → M} {J : Subgroup G} {g : G}
variable {Y : Type} [AddCommGroup Y] [Module ℂ Y] {F : G → Y}
open Classical
namespace CompanionTheory.D.Upq.DoubleCosetLemmas
namespace Meas
theorem _root_.solution (h : Meas dx φ J g) {F : G → ℂ} (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : ℂ} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0) :
    (∑ᶠ z : G ⧸ J, F z.out) * ((dx (φ '' stab J g)).toReal : ℂ) = y * ((dx (φ '' A)).toReal : ℂ) := by
  by_cases hy : y = 0
  · rw [finsum_eq h.finite hR h0 (A := J) subset_rfl (y := 0) (fun k hk => by simp [hF k hk, hy])
      fun k hk s hs => J.mul_mem hk hs.1, hy]
    simp
  have hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A := fun k hk s hs => by
    have h1 := hF _ (J.mul_mem (hA hk) hs.1)
    rw [show k * s * g = k * g * (g⁻¹ * s * g) by group, hR _ _ hs.2, hF k (hA hk), if_pos hk] at h1
    by_contra hn
    exact hy (h1.trans (if_neg hn))
  rw [finsum_eq h.finite hR h0 hA hF hs, ← h.card hA hs, ENNReal.toReal_mul]
  simp only [smul_eq_mul, ENNReal.toReal_natCast]
  push_cast; ring
end Meas
end CompanionTheory.D.Upq.DoubleCosetLemmas
