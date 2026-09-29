-- Prove2me | solution 1 for Erdos180.encodeFiniteGraph_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:50:29.415864+00:00
-- url     : https://prove2.me/submissions/2118d7d6-f44a-48c0-a9c2-4c1b7cd376b4

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Maps

namespace Erdos180

noncomputable section
open SimpleGraph

lemma map_equiv_no_isolated
    {V W : Type*} (graph : SimpleGraph V) (e : V ≃ W)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    ∀ u : W, ∃ v : W, (graph.map e.toEmbedding).Adj u v := by
  intro u
  obtain ⟨v, huv⟩ := hneighbors (e.symm u)
  refine ⟨e v, ?_⟩
  have h :=
    (SimpleGraph.map_adj_apply
      (G := graph) (f := e.toEmbedding)
      (a := e.symm u) (b := v)).mpr huv
  simpa using h

end

end Erdos180

open Erdos180
open SimpleGraph

theorem solution
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    GraphHasNoIsolated (encodeFiniteGraph graph).graph := by
  classical
  exact map_equiv_no_isolated graph (Fintype.equivFin V) hneighbors
