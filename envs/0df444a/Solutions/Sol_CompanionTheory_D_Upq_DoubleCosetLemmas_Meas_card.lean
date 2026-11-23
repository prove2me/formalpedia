-- Prove2me | solution 1 for CompanionTheory.D.Upq.DoubleCosetLemmas.Meas.card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:55.923747+00:00
-- url     : https://prove2.me/submissions/f9ded44c-6b0e-431e-b9a4-19a41b8f0653

import Mathlib
import Definitions.Def_Development_WeilBound_HeckeVectors_HeckeDoubleCosets_DoubleCosetLemmas_LocCount
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_fibre_eq
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_finset
import Theorems.Thm_CompanionTheory_D_Upq_DoubleCosetLemmas_Meas_finite

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
namespace CompanionTheory.D.Upq.DoubleCosetLemmas
namespace Meas
theorem _root_.solution (h : Meas dx φ J g) {A : Set G} (hA : A ⊆ J)
    (hs : ∀ k ∈ A, ∀ s ∈ stab J g, k * s ∈ A) :
    ((cos J g A).ncard : ENNReal) * dx (φ '' stab J g) = dx (φ '' A) := by
  have hsub : cos J g A ⊆ cos J g J := fun z ⟨k, hk, e⟩ => ⟨k, hA hk, e⟩
  have hf := h.finite.subset hsub
  rw [Set.ncard_eq_toFinset_card _ hf, ← h.finset _ (by simpa using hsub)]
  congr 2
  ext x
  simp only [mem_setOf_eq, Finite.mem_toFinset]
  refine ⟨fun ⟨hx, k, hk, e⟩ => ?_, fun hx => ⟨hA hx, x, hx, rfl⟩⟩
  have : x ∈ (k * ·) '' stab J g := fibre_eq (hA hk) ▸ ⟨hx, e⟩
  obtain ⟨s, hs', rfl⟩ := this
  exact hs k hk s hs'
end Meas
end CompanionTheory.D.Upq.DoubleCosetLemmas
