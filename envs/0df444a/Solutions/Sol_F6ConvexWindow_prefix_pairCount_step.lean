-- Prove2me | solution 1 for F6ConvexWindow.prefix_pairCount_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T11:08:39.630818+00:00
-- url     : https://prove2.me/submissions/a62ab93a-1482-48fd-ab66-f6e280e2bfd1

import Definitions.Def_StableMarriageF6_F6ConvexWindowFull
import Definitions.Def_StableMarriageF6_F6ConvexWindowN15
import Theorems.Thm_F6ConvexWindow_mem_tripleUnion
import Theorems.Thm_F6ConvexWindow_pairCount_triple
import Theorems.Thm_F6ConvexWindow_pairCount_union_le
import Theorems.Thm_F6ConvexWindow_disjoint_triples_cross_le_three
import Theorems.Thm_F6ConvexWindow_prefix_overlap_eq_last
import Theorems.Thm_F6ConvexWindow_prefix_crossPairs_subset
import Theorems.Thm_F6ConvexWindow_overlapping_prefix_crossPairs_empty
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
    pairCount (tripleUnion G ∪ T) ≤ pairCount (tripleUnion G) + 3 +
      if Disjoint (tripleUnion G) T then 3 else 0 := by
  have hs := hg S hSG
  have hbase := pairCount_union_le (tripleUnion G) T
  rw [pairCount_triple ht] at hbase
  by_cases hd : Disjoint (tripleUnion G) T
  · rw [if_pos hd]
    have hSTd : Disjoint S T := disjoint_left.mpr
      (fun x hxS hxT => disjoint_left.mp hd (mem_tripleUnion.mpr ⟨S, hSG, hxS⟩) hxT)
    have hc := (card_le_card (prefix_crossPairs_subset hw hci hg hSG hSmax ht hST)).trans
      (disjoint_triples_cross_le_three hw hci hs ht hSTd)
    omega
  · rw [if_neg hd]
    have hover : (S ∩ T).Nonempty := by
      by_contra hn
      apply hd
      apply disjoint_iff_inter_eq_empty.mpr
      rw [inter_comm, prefix_overlap_eq_last hw hci hg hSG hSmax ht hST, inter_comm]
      exact not_nonempty_iff_eq_empty.mp hn
    rw [overlapping_prefix_crossPairs_empty hw hci hg hSG hSmax ht hST hover, card_empty] at hbase
    omega
end F6ConvexWindow
