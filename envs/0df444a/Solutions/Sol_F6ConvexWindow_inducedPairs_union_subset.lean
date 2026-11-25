-- Prove2me | solution 1 for F6ConvexWindow.inducedPairs_union_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:47:54.439496+00:00
-- url     : https://prove2.me/submissions/d283e3ef-2c00-415f-bcaa-8d7476043277

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleFamily
import Theorems.Thm_F6ConvexWindow_card_tripleFamily
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_mem_inducedPairs
import Theorems.Thm_F6ConvexWindow_ChainDecomposition_mem_part
import Theorems.Thm_F6ConvexWindow_antichain_inc
import Theorems.Thm_F6ConvexWindow_inc_symm
import Theorems.Thm_F6ConvexWindow_mem_Inc
import Theorems.Thm_F6ConvexWindow_mem_antichains
import Theorems.Thm_F6ConvexWindow_mem_ideal
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
theorem _root_.solution (U W : Finset V) :
    inducedPairs (U ∪ W) ⊆ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) := by
  classical
  intro P hP
  obtain ⟨hsub, hc, ha⟩ := mem_inducedPairs.mp hP
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hc
  have haUW := hsub (mem_insert_self a {b})
  have hbUW := hsub (mem_insert_of_mem (mem_singleton_self b))
  have hi : IncRel a b := antichain_inc ha (by simp) (by simp) hab
  have addU (haU : a ∈ U) (hbU : b ∈ U) :
      {a, b} ∈ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) :=
    mem_union_left _ (mem_union_left _ (mem_inducedPairs.mpr
      ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨haU, hbU⟩,
        by simp [hab], ha⟩))
  have addW (haW : a ∈ W) (hbW : b ∈ W) :
      {a, b} ∈ inducedPairs U ∪ inducedPairs W ∪ crossPairs (U \ W) (W \ U) :=
    mem_union_left _ (mem_union_right _ (mem_inducedPairs.mpr
      ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨haW, hbW⟩,
        by simp [hab], ha⟩))
  by_cases haU : a ∈ U
  · by_cases hbU : b ∈ U
    · exact addU haU hbU
    · have hbW := (mem_union.mp hbUW).resolve_left hbU
      by_cases haW : a ∈ W
      · exact addW haW hbW
      · exact mem_union_right _ (mem_biUnion.mpr ⟨a, mem_sdiff.mpr ⟨haU, haW⟩,
          mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_sdiff.mpr ⟨hbW, hbU⟩, hi⟩, rfl⟩⟩)
  · have haW := (mem_union.mp haUW).resolve_left haU
    by_cases hbW : b ∈ W
    · exact addW haW hbW
    · have hbU := (mem_union.mp hbUW).resolve_right hbW
      exact mem_union_right _ (mem_biUnion.mpr ⟨b, mem_sdiff.mpr ⟨hbU, hbW⟩,
        mem_image.mpr ⟨a, mem_filter.mpr ⟨mem_sdiff.mpr ⟨haW, haU⟩, inc_symm hi⟩,
          pair_comm b a⟩⟩)
end F6ConvexWindow
