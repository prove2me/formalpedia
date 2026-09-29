-- Prove2me | solution 1 for Erdos183.cliqueFree_pullback_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:20:00.604863+00:00
-- url     : https://prove2.me/submissions/375737fc-41aa-4dea-ad90-9a6941ee0695

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
import Theorems.Thm_Erdos183_labelGraph_pullback_embedding

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V)
    (hC : ∀ colour : K, (C.labelGraph colour).CliqueFree 3) :
    ∀ colour : K, ((C.pullback f).labelGraph colour).CliqueFree 3 := by
  intro colour T hT
  have hmap :
      ((C.pullback f).labelGraph colour).map f ≤ C.labelGraph colour := by
    rw [labelGraph_pullback_embedding]
    exact SimpleGraph.map_comap_le f (C.labelGraph colour)
  exact hC colour (T.map f) (hT.map.mono hmap)
