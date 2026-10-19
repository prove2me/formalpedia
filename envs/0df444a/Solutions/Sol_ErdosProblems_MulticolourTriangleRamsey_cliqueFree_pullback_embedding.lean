-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.cliqueFree_pullback_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/d5c8e54f-d130-4a93-9b37-06052933cfc5

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_labelGraph_pullback_embedding

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {U V K : Type*}
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
end ErdosProblems.MulticolourTriangleRamsey
