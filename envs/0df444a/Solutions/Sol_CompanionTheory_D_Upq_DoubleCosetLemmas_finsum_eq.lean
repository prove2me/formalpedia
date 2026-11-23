-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.finsum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:43.085408+00:00
-- url     : https://prove2.me/submissions/53e94b1b-f249-4f15-875b-fba2484ef291

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_out_eq
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_supp_sub

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
theorem _root_.solution (hf : (cos J g J).Finite) (hR : ∀ z, ∀ k ∈ J, F (z * k) = F z)
    (h0 : ∀ z, z ∉ DoubleCoset.doubleCoset g (J : Set G) J → F z = 0) {A : Set G} (hA : A ⊆ J)
    {y : Y} (hF : ∀ k ∈ J, F (k * g) = if k ∈ A then y else 0)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ∑ᶠ z : G ⧸ J, F z.out = ((cos J g A).ncard : ℂ) • y := by
  have hsub : cos J g A ⊆ cos J g J := fun z ⟨k, hk, e⟩ => ⟨k, hA hk, e⟩
  have hf' := hf.subset hsub
  rw [finsum_eq_sum_of_support_subset (s := hf'.toFinset), Set.ncard_eq_toFinset_card _ hf',
    Finset.sum_congr rfl fun z hz => ?_, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  · obtain ⟨k, hk, rfl⟩ := hf'.mem_toFinset.1 hz
    rw [out_eq hR, hF k (hA hk), if_pos hk]
  · intro z hz
    obtain ⟨k, hk, rfl⟩ := supp_sub h0 hz
    have := hz
    rw [Function.mem_support, out_eq hR, hF k hk] at this
    have hkA : k ∈ A := by by_contra hn; exact this (if_neg hn)
    simpa using ⟨k, hkA, rfl⟩
end CompanionTheory.D.Upq.DoubleCosetLemmas
