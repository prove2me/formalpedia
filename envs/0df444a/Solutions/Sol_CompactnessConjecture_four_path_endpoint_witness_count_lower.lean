-- Prove2me | solution 1 for CompactnessConjecture.four_path_endpoint_witness_count_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/22563582-6faf-4b18-ac96-a4615fb9a7d8

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_card_nonbacktrackingFourPath_lower
import Theorems.Thm_CompactnessConjecture_nonbacktrackingFourPathWitness_injective

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    d * (d - 1) ^ 3 ≤
      Fintype.card (FourPathEndpointWitness G u) := by
  calc
    d * (d - 1) ^ 3 ≤
        Fintype.card (NonbacktrackingFourPath G u) :=
      card_nonbacktrackingFourPath_lower G d hdegree u
    _ ≤ Fintype.card (FourPathEndpointWitness G u) :=
      Fintype.card_le_of_injective
        (nonbacktrackingFourPathWitness G hbip hfour hsix)
        (nonbacktrackingFourPathWitness_injective G hbip hfour hsix)
end CompactnessConjecture
