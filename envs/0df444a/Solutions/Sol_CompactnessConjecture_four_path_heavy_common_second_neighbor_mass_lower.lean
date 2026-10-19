-- Prove2me | solution 1 for CompactnessConjecture.four_path_heavy_common_second_neighbor_mass_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.07668+00:00
-- url     : https://prove2.me/submissions/886d7337-d7a5-464b-98cc-c9b9b03f0772

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_four_path_common_second_neighbor_sum_lower
import Theorems.Thm_CompactnessConjecture_finite_heavy_fiber_mass_half
import Theorems.Thm_CompactnessConjecture_unrelated_four_path_endpoint_card_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hbip : G.IsBipartite)
    (hfour : (SimpleGraph.cycleGraph 4).Free G)
    (hsix : (SimpleGraph.cycleGraph 6).Free G)
    (d : ℕ) (hdegree : ∀ v : V, d ≤ G.degree v) (u : V) :
    ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 2 ≤
      finiteHeavyFiberMass
        (fun v : UnrelatedFourPathEndpoint G u =>
          Fintype.card (CommonSecondNeighbor G u (v : V)))
        (Fintype.card V) (d * (d - 1) ^ 3) := by
  apply finite_heavy_fiber_mass_half
  · exact Fintype.card_pos_iff.mpr ⟨u⟩
  · exact unrelated_four_path_endpoint_card_le G u
  · exact four_path_common_second_neighbor_sum_lower
      G hbip hfour hsix d hdegree u
end CompactnessConjecture
