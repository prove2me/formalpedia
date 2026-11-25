-- Prove2me | solution 1 for F6ConvexWindow.prefix_crossPairs_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:01:37.976966+00:00
-- url     : https://prove2.me/submissions/f239661d-f8bb-4841-af29-5b24dc0d8ef4

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_earlier_prefix_lt_new
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
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
    crossPairs (tripleUnion G \ T) (T \ tripleUnion G) ⊆ crossPairs S T := by
  classical
  intro P hP
  obtain ⟨x, hx, hPx⟩ := mem_biUnion.mp hP
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hPx
  obtain ⟨hy, hxy⟩ := mem_filter.mp hy
  have hyS : y ∉ S := fun h => (mem_sdiff.mp hy).2 (mem_tripleUnion.mpr ⟨S, hSG, h⟩)
  have hxS : x ∈ S := by
    by_contra h
    exact hxy.1 (earlier_prefix_lt_new hw hci hg hSG hSmax ht hST
      (mem_sdiff.mp hx).1 h (mem_sdiff.mp hy).1 hyS).le
  exact mem_biUnion.mpr ⟨x, hxS,
    mem_image.mpr ⟨y, mem_filter.mpr ⟨(mem_sdiff.mp hy).1, hxy⟩, rfl⟩⟩
end F6ConvexWindow
