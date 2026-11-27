-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_left_type_interface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:11:51.723506+00:00
-- url     : https://prove2.me/submissions/d0378456-f992-422d-84d0-ae38547eca34

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
    (kCharge G D w = 3 ∧ betaCharge G D w = 3 ∧
      paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 ∧
      -externalCharge G D w ≤ 4) ∨
    (kCharge G D w = 3 ∧ betaCharge G D w = 2 ∧
      paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 ∧
      -externalCharge G D w ≤ 7) := by
  have hinfo := mem_paper11K3Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hinfo.1 hinfo.2.1
  have hvalues := lemma_7_2_charge_values G hCan hmax hinfo.1 hinfo.2.1
  rcases hprofile with hβ2 | hβ3 | h4
  · rcases hβ2 with ⟨hk, hβ, hcard⟩
    have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 2 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard
    rcases hvalues with hval | hval | hval
    · exact Or.inr ⟨hk, hβ, hdeg, by omega⟩
    · omega
    · omega
  · rcases hβ3 with ⟨hk, hβ, hcard⟩
    have hdeg : paper11LeftDegree (paper11K3Edges G D hCan hmax)
        (paper11K3RightVertices G D hCan hmax) w = 1 := by
      rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
      exact hcard
    rcases hvalues with hval | hval | hval
    · omega
    · exact Or.inl ⟨hk, hβ, hdeg, by omega⟩
    · omega
  · omega
end C6BipartiteDomination
