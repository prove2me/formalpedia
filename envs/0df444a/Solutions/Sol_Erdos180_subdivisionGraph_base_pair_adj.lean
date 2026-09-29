-- Prove2me | solution 1 for Erdos180.subdivisionGraph_base_pair_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:41:09.522276+00:00
-- url     : https://prove2.me/submissions/972a73ad-d2b8-47b7-8ca4-cb23f1ae1480

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]
