-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.labelGraph_pullback_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/1d00b466-99fc-47fe-9217-fecbd5d93cbb

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {U V K : Type*}
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
end ErdosProblems.MulticolourTriangleRamsey
