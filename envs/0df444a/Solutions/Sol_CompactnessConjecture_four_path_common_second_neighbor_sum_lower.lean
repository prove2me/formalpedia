-- Prove2me | solution 1 for CompactnessConjecture.four_path_common_second_neighbor_sum_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/e610a173-1db9-4234-821b-835db1adc33e

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_four_path_endpoint_witness_count_lower
import Theorems.Thm_CompactnessConjecture_fourPathEndpointWitness_card_eq_sum

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
      ∑ v : UnrelatedFourPathEndpoint G u,
        Fintype.card (CommonSecondNeighbor G u (v : V)) := by
  rw [← fourPathEndpointWitness_card_eq_sum G u]
  exact four_path_endpoint_witness_count_lower
    G hbip hfour hsix d hdegree u
end CompactnessConjecture
