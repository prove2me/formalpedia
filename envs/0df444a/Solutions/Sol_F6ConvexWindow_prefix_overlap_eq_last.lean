-- Prove2me | solution 1 for F6ConvexWindow.prefix_overlap_eq_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:51:04.533071+00:00
-- url     : https://prove2.me/submissions/d9ff0745-3b9f-44a4-8b12-377640c9cd28

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_ideal_subset_of_card_le
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_no_reentry
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleUnion

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    {G : Finset (Finset V)} (hg : ∀ R ∈ G, IsTriple R) {S T : Finset V}
    (hSG : S ∈ G) (hSmax : ∀ R ∈ G, (ideal R).card ≤ (ideal S).card)
    (ht : IsTriple T) (hST : ideal S ⊆ ideal T) :
    T ∩ tripleUnion G = T ∩ S := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨hxT, hxU⟩ := mem_inter.mp hx
    obtain ⟨R, hRG, hxR⟩ := mem_tripleUnion.mp hxU
    have hr := hg R hRG
    have hs := hg S hSG
    have hRS := ideal_subset_of_card_le hw hci hr.1 hs.1 hr.2 hs.2 (hSmax R hRG)
    exact mem_inter.mpr ⟨hxT, no_reentry ht.1 hRS hST hxR hxT⟩
  · intro x hx
    obtain ⟨hxT, hxS⟩ := mem_inter.mp hx
    exact mem_inter.mpr ⟨hxT, mem_tripleUnion.mpr ⟨S, hSG, hxS⟩⟩
end F6ConvexWindow
