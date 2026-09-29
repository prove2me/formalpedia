-- Prove2me | solution 1 for Erdos180.cycleGraph_no_isolated
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:49:06.394698+00:00
-- url     : https://prove2.me/submissions/722dd45b-e157-4db7-847e-58ae14176310

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Erdos180
open SimpleGraph

theorem solution (k : ℕ) :
    ∀ u : Fin (k + 2),
      ∃ v : Fin (k + 2),
        (SimpleGraph.cycleGraph (k + 2)).Adj u v := by
  intro u
  refine ⟨u + 1, ?_⟩
  change u + 1 ∈
    (SimpleGraph.cycleGraph (k + 2)).neighborSet u
  rw [SimpleGraph.cycleGraph_neighborSet]
  simp
