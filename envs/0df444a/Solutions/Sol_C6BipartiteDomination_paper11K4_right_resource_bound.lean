-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_right_resource_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:11.913745+00:00
-- url     : https://prove2.me/submissions/87b86122-29f4-4efd-bf77-9e26ad1359e0

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4_right_degree_eq_incident_card
import Theorems.Thm_C6BipartiteDomination_paper11K4_right_degree_eq_one
import Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
import Theorems.Thm_C6BipartiteDomination_paper9_single_repair_resource_bound
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution {D : Finset V}
    (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6) {u : V}
    (hu : u ∈ paper11K4RightVertices G D hCan hmax) :
    8 ≤ paper11K4Resource G D hCan hmax u := by
  classical
  have hTcard := paper11K4_right_degree_eq_incident_card G hCan hmax (u := u)
  rw [paper11K4_right_degree_eq_one G hCan hmax hu] at hTcard
  have hTcard' : (paper11K4IncidentSupports G D hCan hmax u).card = 1 :=
    hTcard.symm
  have hTne : (paper11K4IncidentSupports G D hCan hmax u).Nonempty :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨w, hw⟩ := hTne
  have hTsing : paper11K4IncidentSupports G D hCan hmax u = {w} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hTcard'
    have haw : a = w := by
      have : w ∈ ({a} : Finset V) := by simpa [ha] using hw
      exact (Finset.mem_singleton.mp this).symm
    simpa [haw] using ha
  have hwInfo := mem_paper11K4Supports G (Finset.mem_filter.mp hw).1
  have hwChosen := (Finset.mem_filter.mp hw).2
  have hLegal := paperChosenRepairSet_legal G hCan hmax hwInfo.1 hwInfo.2.1 u
    hwChosen
  have hChosen : ChosenRepairRelation G D w
      (paperChosenRepairSet G D hCan hmax w) u :=
    ⟨hwChosen, hLegal⟩
  have hbound := paper9_single_repair_resource_bound G hCan hmax hLegal.1
    hwInfo.1 hwInfo.2.1 hChosen (Or.inr hwInfo.2.2)
  have hComp : paper11K4Compensation G D hCan hmax u =
      sharedCompensation G D (supportX G D w) u := by
    simp [paper11K4Compensation, hTsing]
  unfold paper11K4Resource
  rw [hComp]
  rcases hbound with h3 | h4
  · omega
  · exact h4.2
end C6BipartiteDomination
