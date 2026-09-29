-- Prove2me | solution 1 for Erdos180.degree_eq_natCard_neighborSet
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:23:52.022047+00:00
-- url     : https://prove2.me/submissions/1ef046c5-b971-40d9-b321-621f9203391d

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite

open Erdos180
open Finset SimpleGraph
open scoped Classical

theorem solution {V : Type*}
    (G : SimpleGraph V) (v : V) [Fintype (G.neighborSet v)] :
    G.degree v = Nat.card (G.neighborSet v) := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.card_neighborSet_eq_degree G v).symm
