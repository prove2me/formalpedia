-- Prove2me | solution 1 for Formalism.HN.finite_supremum_slopes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:27.109875+00:00
-- url     : https://prove2.me/submissions/f704283f-a7c8-463c-98fa-dd01b237d2b1

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
private lemma finSup_mem_zl {R V E : Type*} [Ring R] [AddCommGroup V] [Module R V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ρ : V →+ E) (N : Submodule R V) (x : E) :
    x ∈ zl ρ N ↔ ∃ y ∈ N, ρ y = x := by
  exact Iff.rfl
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
namespace Formalism.HN
theorem _root_.solution : FinSup := by
  intro R V E _ _ _ _ _ _ ρ L S hL hS
  haveI : DiscreteTopology (zl ρ L) := hL.2
  have hmono : ∀ A B : Submodule R V, A ≤ B → zl ρ A ≤ zl ρ B := by
    intro A B h x hx
    rw [finSup_mem_zl] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, h hy, rfl⟩

  have hrev : ∀ A B : Submodule R V, B ≤ L → zl ρ B ≤ zl ρ A → A ≤ L → B ≤ A := by
    intro A B hBL h hAL y hy
    have : ρ y ∈ zl ρ A := h ((finSup_mem_zl ρ B _).mpr ⟨y, hy, rfl⟩)
    obtain ⟨z, hz, hzy⟩ := (finSup_mem_zl ρ A _).mp this
    have := hL.1 (hAL hz) (hBL hy) hzy
    rw [← this]; exact hz
  let g : Set.Iic L → Submodule ℤ (zl ρ L) := fun N => (zl ρ N.1).comap (zl ρ L).subtype
  have hg : StrictMono g := by
    intro A B hAB
    have hle : (A : Submodule R V) ≤ B := le_of_lt hAB
    have hnle : ¬ (B : Submodule R V) ≤ A := not_le_of_gt hAB
    refine lt_of_le_of_ne (Submodule.comap_mono (hmono _ _ hle)) ?_
    intro heq
    apply hnle
    refine hrev A B B.2 ?_ A.2
    intro x hx
    have hxL : x ∈ zl ρ L := hmono _ _ B.2 hx
    have hm : (⟨x, hxL⟩ : zl ρ L) ∈ g B := hx
    rw [← heq] at hm
    exact hm
  haveI : WellFoundedGT (Set.Iic L) := hg.wellFoundedGT
  obtain ⟨t', ht', he⟩ := CompleteLattice.WellFoundedGT.isSupFiniteCompact (Set.Iic L)
    {x | (x : Submodule R V) ∈ S}
  have hU : (t'.image Subtype.val).sup id ≤ L := by
    refine Finset.sup_le fun N hN => ?_
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hN
    exact x.2
  have hkey : t'.sup id ≤ (⟨_, hU⟩ : Set.Iic L) := by
    refine Finset.sup_le fun x hx => ?_
    show (x : Submodule R V) ≤ (t'.image Subtype.val).sup id
    exact Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hx)
  refine ⟨t'.image Subtype.val, ?_, ?_⟩
  · intro N hN
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hN)
    exact ht' hx
  · refine le_antisymm (sSup_le fun N hN => ?_) (Finset.sup_le fun N hN => ?_)
    · have h1 : (⟨N, hS N hN⟩ : Set.Iic L) ≤ sSup {x : Set.Iic L | (x : Submodule R V) ∈ S} :=
        le_sSup hN
      rw [he] at h1
      exact h1.trans hkey
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hN
      exact le_sSup (ht' hx)
end Formalism.HN
