-- Prove2me | solution 1 for Erdos146.ParentSystem.graph_adj_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:12:54.597138+00:00
-- url     : https://prove2.me/submissions/3a0ac97b-fa6c-49b0-bc6b-e930da681076

import Definitions.Def_erdos146_core2
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos146
open Erdos146.ParentSystem
open Filter Finset SimpleGraph
open scoped Topology

theorem solution {V : Type*} (P : ParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔
      v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := by
  rfl
