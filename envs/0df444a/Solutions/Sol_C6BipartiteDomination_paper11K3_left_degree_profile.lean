-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_left_degree_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:04:05.429418+00:00
-- url     : https://prove2.me/submissions/02d0fe85-171f-43bf-bdba-c18f03d18695

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
import Theorems.Thm_C6BipartiteDomination_paper11_chosen_profile
import Theorems.Thm_C6BipartiteDomination_paper11K3_left_degree_eq_chosen_card

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
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w = 1 ∨
    paper11LeftDegree (paper11K3Edges G D hCan hmax)
      (paper11K3RightVertices G D hCan hmax) w = 2 := by
  rw [paper11K3_left_degree_eq_chosen_card G hCan hmax hw]
  have hinfo := mem_paper11K3Supports G hw
  have hprofile := paper11_chosen_profile G hCan hmax hinfo.1 hinfo.2.1
  rcases hprofile with ⟨_, hβ, hcard⟩ | ⟨_, hβ, hcard⟩ | hbad
  · omega
  · omega
  · omega
end C6BipartiteDomination
