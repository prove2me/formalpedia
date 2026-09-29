-- Prove2me | solution 1 for Erdos146.pairParentCoordinateSupport_true_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:15:40.496834+00:00
-- url     : https://prove2.me/submissions/e0e76276-8c11-4b94-8520-fc6133e70d83

import Definitions.Def_erdos146_core2
import Mathlib.Data.Finset.Card

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate true).card =
      pairParentCoordinateOneCount parents coordinate := by
  rfl
