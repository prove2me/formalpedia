-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_left_debt_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:07.263961+00:00
-- url     : https://prove2.me/submissions/2fece5ff-6e3e-45d5-b3a1-5afbef233d0a

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
import Theorems.Thm_C6BipartiteDomination_paper11_chosen_profile
import Theorems.Thm_C6BipartiteDomination_paper11K3_left_degree_eq_chosen_card
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_charge_values


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K3Supports G D) :
    -externalCharge G D w ≤
      if paper11LeftDegree (paper11K3Edges G D hCan hmax)
          (paper11K3RightVertices G D hCan hmax) w = 1 then 4 else 7 := by
  have hinfo := mem_paper11K3Supports G hw
  have hvalues := lemma_7_2_charge_values G hCan hmax hinfo.1 hinfo.2.1
  have hprofile := paper11_chosen_profile G hCan hmax hinfo.1 hinfo.2.1
  rcases hprofile with ⟨_, hβ2, hcard2⟩ | ⟨_, hβ3, hcard1⟩ | hbad
  · have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard2
    rcases hvalues with hval | hval | hval <;> omega
  · have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard1
    rcases hvalues with hval | hval | hval <;> omega
  · omega
end C6BipartiteDomination
