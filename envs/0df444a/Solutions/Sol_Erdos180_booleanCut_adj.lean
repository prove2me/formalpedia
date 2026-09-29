-- Prove2me | solution 1 for Erdos180.booleanCut_adj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:24:33.745975+00:00
-- url     : https://prove2.me/submissions/1da03a84-d4ec-48fa-8b72-0d14da35eac4

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open Finset SimpleGraph
open scoped Classical

@[simp]
theorem solution {V : Type*} (G : SimpleGraph V)
    (color : V → Bool) (u v : V) :
    (booleanCut G color).Adj u v ↔ G.Adj u v ∧ color u ≠ color v :=
  Iff.rfl
