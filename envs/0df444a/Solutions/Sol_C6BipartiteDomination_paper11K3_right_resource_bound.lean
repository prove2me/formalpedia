-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_right_resource_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:06.244015+00:00
-- url     : https://prove2.me/submissions/0efbf91b-e585-4e87-b20f-7f1e91c18dfc

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_profile
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_one_resource
import Theorems.Thm_C6BipartiteDomination_paper11K3_degree_two_compensation_cases

set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    (if paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 1 then 4 else 11) ≤
      paper11K3AvailableResource G D hCan hmax u := by
  classical
  rcases paper11K3_right_degree_profile G hCan hmax hu with h1 | h2
  · have hbase := paper11K3_right_degree_one_resource G hCan hmax hu h1
    unfold paper11K3AvailableResource
    split <;> simp_all <;> omega
  · rcases paper11K3_degree_two_compensation_cases G hCan hmax hu h2 with
      hcase | hcase
    · rcases hcase with ⟨hx, hcharge, hcomp⟩
      unfold paper11K3AvailableResource
      rw [hcharge, hcomp]
      simp
      split <;> omega
    · rcases hcase with ⟨hx, hcharge, q, hcomp, hqcharge, hqQ,
        hdata, howner⟩
      have hbudget : u ∈ paper11K3SpecialBudgetVertices G D hCan hmax := by
        simp [paper11K3SpecialBudgetVertices, hu, hx, h2]
      unfold paper11K3AvailableResource
      rw [hcharge, hcomp]
      simp [hbudget, hqcharge, h2]
end C6BipartiteDomination
