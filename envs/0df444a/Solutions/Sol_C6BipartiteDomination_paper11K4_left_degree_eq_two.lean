-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_left_degree_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:05:37.322165+00:00
-- url     : https://prove2.me/submissions/8fcb5d75-2dd0-44a1-bb24-bb7981e24e08

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4_left_degree_eq_chosen_card
import Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
import Theorems.Thm_C6BipartiteDomination_paper11_chosen_profile


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {w : V}
    (hw : w ∈ paper11K4Supports G D) :
    paper11LeftDegree (paper11K4Edges G D hCan hmax)
      (paper11K4RightVertices G D hCan hmax) w = 2 := by
  rw [paper11K4_left_degree_eq_chosen_card G hCan hmax hw]
  have hwInfo := mem_paper11K4Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hwInfo.1 hwInfo.2.1
  rcases hprofile with h | h | h <;> omega
end C6BipartiteDomination
