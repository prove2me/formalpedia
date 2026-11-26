-- Prove2me | solution 1 for Erdos1007.completeBipartiteGraph_three_three_unitDistance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:54:10.714514+00:00
-- url     : https://prove2.me/submissions/83f881c4-f5f1-4c9d-a3e2-bbf92ac017ee

module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Definitions.Def_Erdos1007_Geometry_CompleteBipartite
public import Theorems.Thm_Erdos1007_completeBipartiteGraph_three_three_unitDistance_with_left

set_option autoImplicit false
@[expose] public section
open Erdos1007
public section
namespace Erdos1007
theorem _root_.solution :
    ∃ f : Fin 3 ⊕ Fin 3 → EuclideanSpace ℝ (Fin 4), Function.Injective f ∧
      ∀ u v, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj u v → dist (f u) (f v) = 1 := by
  obtain ⟨f, hfInj, hfDist, _⟩ := completeBipartiteGraph_three_three_unitDistance_with_left
  exact ⟨f, hfInj, hfDist⟩
end Erdos1007
