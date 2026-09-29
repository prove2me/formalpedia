-- Prove2me | solution 1 for Erdos146.pairGraphCopy_child_layer_side_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:40:12.395162+00:00
-- url     : https://prove2.me/submissions/c920cde6-9976-460c-b9b5-ff0e05abd836

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.InformationTheory.Hamming
import Theorems.Thm_Erdos146_hammingHost_adj_iff
import Theorems.Thm_Erdos146_pairGraph_parent_child_adj

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairGraphCopy_layer_side_eq
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize layer) :
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth layer (by omega) second)).val.1 := by
  classical
  by_cases hequal : first = second
  · subst second
    rfl
  · let bridge : PairLayer baseSize (layer + 1) :=
      ⟨{first, second}, Finset.card_pair hequal⟩
    have hfirst_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) first) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge first
        (by simp [bridge])
    have hsecond_source :
        (pairParentSystem baseSize depth).graph.Adj
          (pairLayerEmbedding baseSize depth (layer + 1) hlayer bridge)
          (pairLayerEmbedding baseSize depth layer (by omega) second) :=
      pairGraph_parent_child_adj baseSize depth layer hlayer bridge second
        (by simp [bridge])
    have hfirst_edge := copy.toHom.map_rel hfirst_source
    have hsecond_edge := copy.toHom.map_rel hsecond_source
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val at hfirst_edge
    change
      (hammingHost dimension radius).Adj
        (copy
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer bridge)).val
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val at hsecond_edge
    have hfirst_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
    have hsecond_side :=
      (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
    cases hbridge :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer bridge)).val.1 <;>
      cases hfirst :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) first)).val.1 <;>
      cases hsecond :
        (copy
          (pairLayerEmbedding baseSize depth layer
            (by omega) second)).val.1 <;>
      simp_all

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {baseSize depth dimension radius : ℕ}
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (pairParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : PairLayer baseSize (layer + 1)) :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 =
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer second)).val.1 := by
  classical
  have hfirst_nonempty : first.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [first.property]
    norm_num
  have hsecond_nonempty : second.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [second.property]
    norm_num
  obtain ⟨firstParent, hfirstParent⟩ := hfirst_nonempty
  obtain ⟨secondParent, hsecondParent⟩ := hsecond_nonempty
  have hparent_side := pairGraphCopy_layer_side_eq
    retained copy layer hlayer firstParent secondParent
  have hfirst_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer first firstParent hfirstParent)
  have hsecond_edge := copy.toHom.map_rel
    (pairGraph_parent_child_adj
      baseSize depth layer hlayer second secondParent hsecondParent)
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer first)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val at hfirst_edge
  change
    (hammingHost dimension radius).Adj
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val at hsecond_edge
  have hfirst_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
  have hsecond_side :=
    (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
  cases hfirst :
    (copy
      (pairLayerEmbedding baseSize depth (layer + 1)
        hlayer first)).val.1 <;>
    cases hsecond :
      (copy
        (pairLayerEmbedding baseSize depth (layer + 1)
          hlayer second)).val.1 <;>
    cases hfirstParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) firstParent)).val.1 <;>
    cases hsecondParent_side :
      (copy
        (pairLayerEmbedding baseSize depth layer
          (by omega) secondParent)).val.1 <;>
    simp_all
