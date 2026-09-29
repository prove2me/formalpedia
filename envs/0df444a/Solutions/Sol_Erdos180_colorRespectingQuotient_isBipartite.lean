-- Prove2me | solution 1 for Erdos180.colorRespectingQuotient_isBipartite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:27:35.505104+00:00
-- url     : https://prove2.me/submissions/1ef699e1-ebd5-4f52-9a05-629f236ba2e6

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Finset SimpleGraph

theorem solution
    {V : Type*} (graph : SimpleGraph V) (color : V → Bool)
    (hproper : ∀ ⦃u v : V⦄, graph.Adj u v → color u ≠ color v)
    (f : V → V) (hf : ColorRespecting color f) :
    (quotientGraph graph f).IsBipartite := by
  classical
  let representative : Set.range f → V :=
    fun vertex => Classical.choose vertex.property
  have hrepresentative (vertex : Set.range f) :
      f (representative vertex) = (vertex : V) :=
    Classical.choose_spec vertex.property
  let quotientColor : Set.range f → Bool :=
    fun vertex => color (representative vertex)
  have hdirected {u v : Set.range f}
      (h : quotientRelation graph f u v) :
      quotientColor u ≠ quotientColor v := by
    rcases h with ⟨x, y, hx, hy, hxy⟩
    change color (representative u) ≠ color (representative v)
    intro heq
    apply hproper hxy
    calc
      color x = color (representative u) :=
        (hf (representative u) x
          ((hrepresentative u).trans hx.symm)).symm
      _ = color (representative v) := heq
      _ = color y :=
        hf (representative v) y
          ((hrepresentative v).trans hy.symm)
  have hcoloring : (quotientGraph graph f).Coloring Bool :=
    SimpleGraph.Coloring.mk quotientColor (by
      intro u v hadj
      change (SimpleGraph.fromRel (quotientRelation graph f)).Adj u v at hadj
      rcases
          (SimpleGraph.fromRel_adj (quotientRelation graph f) u v).mp hadj with
        ⟨_, hforward | hbackward⟩
      · exact hdirected hforward
      · exact Ne.symm (hdirected hbackward))
  simpa using hcoloring.colorable
