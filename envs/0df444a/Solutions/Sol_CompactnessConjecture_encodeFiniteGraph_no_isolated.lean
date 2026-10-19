-- Prove2me | solution 1 for CompactnessConjecture.encodeFiniteGraph_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/f0539533-b995-41da-ba13-56ca9b6ea4a7

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_map_equiv_no_isolated

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    GraphHasNoIsolated (encodeFiniteGraph graph).graph := by
  classical
  exact map_equiv_no_isolated graph (Fintype.equivFin V) hneighbors
end CompactnessConjecture
