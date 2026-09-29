-- Prove2me | solution 1 for Erdos180.edgeFinset_card_eq_natCard
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T02:23:10.268715+00:00
-- url     : https://prove2.me/submissions/8a7ff9b4-bdbb-489f-8e22-0b85493713e4

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.SetTheory.Cardinal.Finite

open Erdos180
open Finset SimpleGraph
open scoped Classical

theorem solution {V : Type*} (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    G.edgeFinset.card = Nat.card G.edgeSet := by
  simpa only [Nat.card_eq_fintype_card] using
    (SimpleGraph.edgeFinset_card (G := G))
