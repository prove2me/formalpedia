-- Prove2me | solution 1 for CompactnessConjecture.booleanCut_deleteIncidence_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/ad38bfa3-620f-4aa7-af09-fcda27100837

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
open scoped Classical
namespace CompactnessConjecture
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (color : V → Bool) (v : V) :
    (booleanCut G (flipBooleanColor color v)).deleteIncidenceSet v =
      (booleanCut G color).deleteIncidenceSet v := by
  ext x y
  simp only [SimpleGraph.deleteIncidenceSet_adj, booleanCut_adj]
  by_cases hx : x = v
  · subst x
    simp
  by_cases hy : y = v
  · subst y
    simp
  simp [flipBooleanColor, hx, hy]
end CompactnessConjecture
