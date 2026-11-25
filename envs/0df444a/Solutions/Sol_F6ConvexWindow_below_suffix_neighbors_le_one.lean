-- Prove2me | solution 1 for F6ConvexWindow.below_suffix_neighbors_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:59:24.596535+00:00
-- url     : https://prove2.me/submissions/656de84a-7b40-45c7-bf1f-6cfc2e0b8aea

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_later_exclusive_above
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_below_lt_above
import Theorems.Thm_F6ConvexWindow_ideal_subset_of_card_le
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_triple_incomparables_le_one
attribute [local simp] F6ConvexWindow.ChainDecomposition.mem_part
attribute [local simp] F6ConvexWindow.mem_Inc
attribute [local simp] F6ConvexWindow.mem_antichains
attribute [local simp] F6ConvexWindow.mem_ideal


attribute [local simp] F6ConvexWindow.mem_tripleFamily
attribute [local simp] F6ConvexWindow.card_tripleFamily
attribute [local simp] F6ConvexWindow.mem_tripleUnion
attribute [local simp] F6ConvexWindow.mem_inducedPairs

set_option autoImplicit true
noncomputable section
open F6ConvexWindow
open Finset
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false
variable {V : Type*} [Fintype V] [PartialOrder V]
namespace F6ConvexWindow
theorem _root_.solution (hw : WidthLE (V := V) 3) (hci : CI2 (V := V))
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) (hb : ∀ T ∈ F, Below T x) :
    ((tripleUnion F).filter (IncRel x)).card ≤ 1 := by
  classical
  by_cases hn : F.Nonempty
  · obtain ⟨S, hSF, hSmin⟩ := exists_min_image F (fun T => (ideal T).card) hn
    have hs := hf S hSF
    have hxs : x ∉ S := fun h => hx (mem_tripleUnion.mpr ⟨S, hSF, h⟩)
    apply (card_le_card (show (tripleUnion F).filter (IncRel x) ⊆ S.filter (IncRel x) from ?_)).trans
      (triple_incomparables_le_one hw hci hs.1 hs.2 hxs)
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨?_, hxy⟩
    by_contra hyS
    obtain ⟨R, hRF, hyR⟩ := mem_tripleUnion.mp hyU
    have hr := hf R hRF
    have hSR := ideal_subset_of_card_le hw hci hs.1 hr.1 hs.2 hr.2 (hSmin R hRF)
    exact hxy.1 (below_lt_above hs.2 (hb S hSF)
      (later_exclusive_above hw hci hs hr hSR hyR hyS)).le
  · rw [not_nonempty_iff_eq_empty.mp hn]
    simp [tripleUnion]
end F6ConvexWindow
