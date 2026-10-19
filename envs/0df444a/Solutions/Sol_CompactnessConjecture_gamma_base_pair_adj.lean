-- Prove2me | solution 1 for CompactnessConjecture.gamma_base_pair_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/85e562ea-cb81-4dda-b284-99427a62f188

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution (base : Fin 3) (center : Fin 3) :
    gammaGraph.Adj
      (.inl (.inl base)) (.inr (base, center)) := by
  simp [SubdivisionGraph, SimpleGraph.fromRel_adj,
    subdivisionRelation]
end CompactnessConjecture
