-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_right_degree_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:13.249164+00:00
-- url     : https://prove2.me/submissions/9df4baaa-9052-471f-9545-5cddcb93b5d9

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4_right_degree_eq_incident_card
import Theorems.Thm_C6BipartiteDomination_mem_paper11K4Supports
import Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_eq_one_at_k4


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
    paper11RightDegree (paper11K4Edges G D hCan hmax)
      (paper11K4Supports G D) u = 1 := by
  have hB : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  have hInc : (paper11K4IncidentSupports G D hCan hmax u).Nonempty :=
    (Finset.mem_filter.mp hu).2
  obtain ⟨w, hw⟩ := hInc
  have hwInfo := mem_paper11K4Supports G (Finset.mem_filter.mp hw).1
  let T := paper11NegativeIncidentSupports G D hCan hmax u
  have hTsub : T ⊆ SPart G D := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).1
  have hTneg : ∀ v ∈ T, externalCharge G D v < 0 := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
  have hTrepair : ∀ v ∈ T, u ∈ paperChosenRepairSet G D hCan hmax v := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hwT : w ∈ T := by
    simp [T, paper11NegativeIncidentSupports, paper11NegativeSupports,
      hwInfo.1, hwInfo.2.1, (Finset.mem_filter.mp hw).2]
  have hTall : T.card = 1 :=
    paper9_repair_degree_eq_one_at_k4 G hCan hmax (w₄ := w) hB T
      hTsub hTneg hTrepair hwT hwInfo.2.2
  have hT4sub : paper11K4IncidentSupports G D hCan hmax u ⊆ T := by
    intro v hv
    have hi := Finset.mem_filter.mp hv
    have info := mem_paper11K4Supports G hi.1
    simp only [T, paper11NegativeIncidentSupports, paper11NegativeSupports,
      Finset.mem_filter]
    exact ⟨⟨info.1, info.2.1⟩, hi.2⟩
  have hT4pos : 0 < (paper11K4IncidentSupports G D hCan hmax u).card :=
    Finset.card_pos.mpr ⟨w, hw⟩
  have hT4card : (paper11K4IncidentSupports G D hCan hmax u).card = 1 := by
    have := Finset.card_le_card hT4sub
    omega
  rw [paper11K4_right_degree_eq_incident_card G hCan hmax]
  exact hT4card
end C6BipartiteDomination
