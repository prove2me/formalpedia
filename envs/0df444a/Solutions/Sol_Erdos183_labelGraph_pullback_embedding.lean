-- Prove2me | solution 1 for Erdos183.labelGraph_pullback_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-04T00:19:29.222937+00:00
-- url     : https://prove2.me/submissions/585d4e18-846f-4b00-a7ed-7d5b479c77ca

import Definitions.Def_erdos183_core
import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling

open Filter Finset SimpleGraph
open scoped Topology

open Erdos183

theorem solution {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K) :
    (C.pullback f).labelGraph colour = (C.labelGraph colour).comap f := by
  ext x y
  change
    ((C.pullback f).labelGraph colour).Adj x y ↔
      (C.labelGraph colour).Adj (f x) (f y)
  constructor
  · intro hadj
    obtain ⟨hxy, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj (f x) (f y)).mpr
    refine ⟨f.injective.ne hxy, ?_⟩
    simpa [SimpleGraph.EdgeLabeling.get,
      SimpleGraph.EdgeLabeling.pullback, SimpleGraph.Hom.mapEdgeSet] using hcolour
  · intro hadj
    obtain ⟨hxy, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj (f x) (f y)).mp hadj
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mpr
    refine ⟨fun heq => hxy (congrArg f heq), ?_⟩
    simpa [SimpleGraph.EdgeLabeling.get,
      SimpleGraph.EdgeLabeling.pullback, SimpleGraph.Hom.mapEdgeSet] using hcolour
