-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_right_degree_one_resource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:12.084221+00:00
-- url     : https://prove2.me/submissions/b22d17e5-606a-4095-a128-54039fdecb95

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_eq_incident_card
import Theorems.Thm_C6BipartiteDomination_paper9_single_repair_resource_bound
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K3RightVertices G D hCan hmax)
    (hdeg : paper11RightDegree (paper11K3Edges G D hCan hmax)
      (paper11K3Supports G D) u = 1) :
    4 ≤ vertexCharge G D u +
      ∑ q ∈ paper11K3Compensation G D hCan hmax u, externalCharge G D q := by
  classical
  have hcard := paper11K3_right_degree_eq_incident_card G hCan hmax (u := u)
  rw [hcard] at hdeg
  have hTne : (paper11K3IncidentSupports G D hCan hmax u).Nonempty :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨w, hw⟩ := hTne
  have hTcard : (paper11K3IncidentSupports G D hCan hmax u).card = 1 := hdeg
  obtain ⟨v, hTv⟩ := Finset.card_eq_one.mp hTcard
  have hvw : v = w := by
    have hwv : w ∈ ({v} : Finset V) := by simpa [hTv] using hw
    exact (Finset.mem_singleton.mp hwv).symm
  have hTsing : paper11K3IncidentSupports G D hCan hmax u = {w} := by
    simpa [hvw] using hTv
  have hwInfo := mem_paper11K3Supports G (Finset.mem_filter.mp hw).1
  have hlegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u
    (Finset.mem_filter.mp hw).2
  have hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u :=
    ⟨(Finset.mem_filter.mp hw).2, hlegal⟩
  obtain h3 | h4 := paper9_single_repair_resource_bound G hCan hmax hlegal.1
      hwInfo.1 hwInfo.2.1 hChosen (Or.inl hwInfo.2.2)
  · have hUnion : paper11K3Compensation G D hCan hmax u =
        sharedCompensation G D (supportX G D w) u := by
      simp [paper11K3Compensation, hTsing]
    rw [hUnion]
    exact h3.2
  · omega
end C6BipartiteDomination
