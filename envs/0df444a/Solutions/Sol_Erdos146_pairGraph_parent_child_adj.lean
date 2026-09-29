-- Prove2me | solution 1 for Erdos146.pairGraph_parent_child_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:13:35.98476+00:00
-- url     : https://prove2.me/submissions/4d2a5b02-9f96-4980-8227-b3d53cef26f5

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Basic
import Theorems.Thm_Erdos146_ParentSystem_graph_adj_iff

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : PairLayer baseSize (layer + 1))
    (parent : PairLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (pairParentSystem baseSize depth).graph.Adj
      (pairLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (pairLayerEmbedding baseSize depth layer (by omega) parent) := by
  apply (ParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : PairVertex baseSize depth => vertex.1.val)
      hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        pairParents baseSize depth
          (pairLayerEmbedding baseSize depth (layer + 1)
            hlayer child)
    change
      pairLayerEmbedding baseSize depth layer (by omega) parent ∈
        child.val.map
          (pairLayerEmbedding baseSize depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
