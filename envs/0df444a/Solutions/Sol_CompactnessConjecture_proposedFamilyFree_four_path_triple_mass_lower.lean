-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_four_path_triple_mass_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:00.811989+00:00
-- url     : https://prove2.me/submissions/3e305077-00a6-4769-9297-807d082001a3

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_four_cycle
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_six_cycle
import Theorems.Thm_CompactnessConjecture_four_path_common_second_neighbor_triple_mass_lower

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace CompactnessConjecture
theorem _root_.solution
    {n : ℕ} (host : SimpleGraph (Fin n))
    [DecidableRel host.Adj]
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin n, d ≤ host.degree v)
    (u : Fin n)
    (hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold n (d * (d - 1) ^ 3)) :
    fourPathHeavyThreshold n (d * (d - 1) ^ 3) ^ 2 *
        ((d * (d - 1) ^ 3 : ℕ) : ℝ) / 54 ≤
      (commonSecondNeighborTripleMass host u : ℝ) := by
  have hthreshold' : (3 : ℝ) ≤
      fourPathHeavyThreshold (Fintype.card (Fin n))
        (d * (d - 1) ^ 3) := by
    simpa using hthreshold
  simpa using four_path_common_second_neighbor_triple_mass_lower
    host hbip (proposedFamilyFree_four_cycle hfree)
    (proposedFamilyFree_six_cycle hfree) d hdegree u hthreshold'
end CompactnessConjecture
