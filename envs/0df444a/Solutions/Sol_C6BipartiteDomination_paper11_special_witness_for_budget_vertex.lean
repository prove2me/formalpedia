-- Prove2me | solution 1 for C6BipartiteDomination.paper11_special_witness_for_budget_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:09:03.083883+00:00
-- url     : https://prove2.me/submissions/2121a831-5bd0-4032-984f-aa5bf82ebedc

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
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
    (hu : u ∈ paper11K3SpecialBudgetVertices G D hCan hmax) :
    ∃ q, q ∈ paper10SpecialQSet G hCan hmax ∧
      ∃ data : Paper10SpecialWitness G hCan hmax q, data.u = u := by
  have huR : u ∈ paper11K3RightVertices G D hCan hmax :=
    (Finset.mem_filter.mp hu).1
  have hx : xCharge G D u = 0 := (Finset.mem_filter.mp hu).2.1
  have hdeg : paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u = 2 := (Finset.mem_filter.mp hu).2.2
  rcases paper11K3_degree_two_compensation_cases G hCan hmax huR hdeg with
    hcase | hcase
  · omega
  · obtain ⟨hxcase, _, q, _, _, hqQ, data, howner⟩ := hcase
    exact ⟨q, hqQ, data, howner⟩
end C6BipartiteDomination
