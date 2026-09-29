-- Prove2me | solution 1 for Erdos146.pairTypeGroup_false_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T05:17:03.819215+00:00
-- url     : https://prove2.me/submissions/42c8c69e-d335-4598-bc94-cb5d5d221bdb

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Theorems.Thm_Erdos146_pairParentCoordinateSupport_true_card
import Theorems.Thm_Erdos146_pairTypeGroup_homogeneous_card

namespace Erdos146

section
open Filter Finset SimpleGraph
open scoped Topology

theorem pairParentCoordinateSupport_card_add
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card +
      (pairParentCoordinateSupport parents coordinate true).card =
        parentCount := by
  classical
  have hpartition :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin parentCount)))
      (fun parent => parents parent coordinate = false)
  simpa [pairParentCoordinateSupport, Bool.not_eq_false] using hpartition

theorem pairParentCoordinateSupport_false_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairParentCoordinateSupport parents coordinate false).card =
      parentCount - pairParentCoordinateOneCount parents coordinate := by
  have hpartition := pairParentCoordinateSupport_card_add parents coordinate
  rw [pairParentCoordinateSupport_true_card] at hpartition
  omega

end

end Erdos146

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem solution
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (pairTypeGroup parents coordinate 0).card =
      (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 := by
  simpa [pairParentCoordinateSupport_false_card] using
    pairTypeGroup_homogeneous_card parents coordinate false
