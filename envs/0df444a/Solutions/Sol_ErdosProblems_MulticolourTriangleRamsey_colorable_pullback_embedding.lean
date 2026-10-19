-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.colorable_pullback_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/bb8c3e58-5afb-4496-b12f-14e07f7e9cd4

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_labelGraph_pullback_embedding

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution {U V K : Type*} {j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K)
    (hC : (C.labelGraph colour).Colorable j) :
    ((C.pullback f).labelGraph colour).Colorable j := by
  obtain ⟨label⟩ := hC
  refine ⟨SimpleGraph.Coloring.mk (fun u => label (f u)) ?_⟩
  intro u v hadj
  apply label.valid
  rw [labelGraph_pullback_embedding] at hadj
  exact hadj
end ErdosProblems.MulticolourTriangleRamsey
