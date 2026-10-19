-- Prove2me | solution 1 for CompactnessConjecture.card_nonbacktrackingNeighbor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/b558b774-d3ad-4288-878f-3ab86b5d404e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {previous current : V} (hedge : G.Adj current previous) :
    Fintype.card (NonbacktrackingNeighbor G previous current) =
      G.degree current - 1 := by
  classical
  calc
    Fintype.card (NonbacktrackingNeighbor G previous current) =
        ((G.neighborFinset current).erase previous).card := by
      rw [Fintype.card_subtype]
      congr 1
      ext next
      simp [and_comm]
    _ = G.degree current - 1 := by
      rw [Finset.card_erase_of_mem]
      · rfl
      · simpa using hedge
end CompactnessConjecture
