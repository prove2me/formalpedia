-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.cliqueFree_compRight_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/279d594f-9a62-4eb3-87e9-298039c1ef28

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {V K K' : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (e : K ↪ K')
    (hC : ∀ colour : K, (C.labelGraph colour).CliqueFree 3) :
    ∀ colour : K', ((C.compRight e).labelGraph colour).CliqueFree 3 := by
  classical
  intro colour T hT
  obtain ⟨x, y, z, hxy, hxz, hyz, _⟩ :=
    (SimpleGraph.is3Clique_iff).mp hT
  obtain ⟨hxyne, hxycolour⟩ :=
    (SimpleGraph.TopEdgeLabeling.labelGraph_adj x y).mp hxy
  change e (C.get x y hxyne) = colour at hxycolour
  let old : K := C.get x y hxyne
  have reflect {u v : V}
      (hadj : ((C.compRight e).labelGraph colour).Adj u v) :
      (C.labelGraph old).Adj u v := by
    obtain ⟨hne, hcolour⟩ :=
      (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mp hadj
    change e (C.get u v hne) = colour at hcolour
    apply (SimpleGraph.TopEdgeLabeling.labelGraph_adj u v).mpr
    refine ⟨hne, ?_⟩
    exact e.injective (hcolour.trans hxycolour.symm)
  exact hC old {x, y, z}
    ((SimpleGraph.is3Clique_triple_iff).mpr
      ⟨reflect hxy, reflect hxz, reflect hyz⟩)
end ErdosProblems.MulticolourTriangleRamsey
