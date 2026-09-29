-- Prove2me | solution 1 for Erdos180.subdivisionGraph_center_pair_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:41:51.017764+00:00
-- url     : https://prove2.me/submissions/518ac5a9-e58e-4bcc-bdd3-c7b1cbe419bc

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem solution
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]
