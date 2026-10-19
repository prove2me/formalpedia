-- Prove2me | solution 1 for CompactnessConjecture.girthEight_degree_mul_pred_sq_le_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/dc1ba1c0-2997-443f-b9b7-f55c62218090

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_card_nonbacktrackingThreePath_lower
import Theorems.Thm_CompactnessConjecture_nonbacktrackingThreePathEndpoint_injective

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
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v)
    (u : V) :
    G.degree u * (d - 1) ^ 2 ≤ Fintype.card V := by
  calc
    G.degree u * (d - 1) ^ 2 ≤
        Fintype.card (NonbacktrackingThreePath G u) :=
      card_nonbacktrackingThreePath_lower G d hdegree u
    _ ≤ Fintype.card V :=
      Fintype.card_le_of_injective
        (nonbacktrackingThreePathEndpoint G)
        (nonbacktrackingThreePathEndpoint_injective
          G hbip hfour hsix)
end CompactnessConjecture
