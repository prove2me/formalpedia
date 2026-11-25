-- Prove2me | solution 1 for F6ConvexWindow.outsider_neighbors_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:06:12.645536+00:00
-- url     : https://prove2.me/submissions/61969294-ab63-4d33-b1c7-ce6c92fe07c5

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_above_prefix_neighbors_le_one
import Theorems.Thm_F6ConvexWindow_below_suffix_neighbors_le_one
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
import Theorems.Thm_F6ConvexWindow_triple_split
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
    (F : Finset (Finset V)) (hf : ∀ T ∈ F, IsTriple T) {x : V}
    (hx : x ∉ tripleUnion F) : ((tripleUnion F).filter (IncRel x)).card ≤ 2 := by
  classical
  let A := F.filter (fun T => Above T x)
  let B := F.filter (fun T => Below T x)
  have hxF (G : Finset (Finset V)) (hG : G ⊆ F) : x ∉ tripleUnion G := by
    intro h
    obtain ⟨T, hTG, hxT⟩ := mem_tripleUnion.mp h
    exact hx (mem_tripleUnion.mpr ⟨T, hG hTG, hxT⟩)
  have hA := above_prefix_neighbors_le_one hw hci A
    (fun T hT => hf T (mem_filter.mp hT).1) (hxF A (filter_subset _ _))
    (fun T hT => (mem_filter.mp hT).2)
  have hB := below_suffix_neighbors_le_one hw hci B
    (fun T hT => hf T (mem_filter.mp hT).1) (hxF B (filter_subset _ _))
    (fun T hT => (mem_filter.mp hT).2)
  have hcover : (tripleUnion F).filter (IncRel x) ⊆
      (tripleUnion A).filter (IncRel x) ∪ (tripleUnion B).filter (IncRel x) := by
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_filter.mp hy
    obtain ⟨T, hTF, hyT⟩ := mem_tripleUnion.mp hyU
    have ht := hf T hTF
    have hxT : x ∉ T := fun h => hx (mem_tripleUnion.mpr ⟨T, hTF, h⟩)
    rcases triple_split hw hci ht.1 ht.2 hxT with hl | hu
    · exact mem_union_right _ (mem_filter.mpr
        ⟨mem_tripleUnion.mpr ⟨T, mem_filter.mpr ⟨hTF, hl⟩, hyT⟩, hxy⟩)
    · exact mem_union_left _ (mem_filter.mpr
        ⟨mem_tripleUnion.mpr ⟨T, mem_filter.mpr ⟨hTF, hu⟩, hyT⟩, hxy⟩)
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  omega
end F6ConvexWindow
