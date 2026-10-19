-- Prove2me | solution 1 for CompactnessConjecture.subdivisionGraph_center_pair_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:58.946881+00:00
-- url     : https://prove2.me/submissions/30012a4e-504b-481b-b3c5-efa0e8c60063

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inr center)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]
end CompactnessConjecture
