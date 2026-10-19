-- Prove2me | solution 1 for CompactnessConjecture.independentThetaTriple_card_le_orderedThetaTripleCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/a69f83cb-d5f5-4dd4-b8d6-b62b5b625563

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_independentThetaTripleOrderedWitness_injective
import Theorems.Thm_CompactnessConjecture_orderedThetaWitness_card

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    (hbip : host.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free host)
    (hsix : (SimpleGraph.cycleGraph 6).Free host) :
    Fintype.card (IndependentThetaTriple host) ≤
      orderedThetaTripleCount host := by
  calc
    Fintype.card (IndependentThetaTriple host) ≤
        Fintype.card (OrderedThetaWitness host) :=
      Fintype.card_le_of_injective
        (independentThetaTripleOrderedWitness host hbip hfour hsix)
        (independentThetaTripleOrderedWitness_injective
          host hbip hfour hsix)
    _ = orderedThetaTripleCount host := orderedThetaWitness_card host
end CompactnessConjecture
