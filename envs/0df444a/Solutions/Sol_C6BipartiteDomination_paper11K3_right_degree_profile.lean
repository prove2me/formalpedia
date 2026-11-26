-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_right_degree_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:06:10.952581+00:00
-- url     : https://prove2.me/submissions/0499519b-f15e-4d0f-975c-d4cafc2e8c25

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_eq_incident_card
import Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_le_two


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
    paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 1 ∨
    paper11RightDegree (paper11K3Edges G D hCan hmax)
        (paper11K3Supports G D) u = 2 := by
  rw [paper11K3_right_degree_eq_incident_card G hCan hmax]
  have hU : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  have hInc := (Finset.mem_filter.mp hu).2
  have hne : (paper11K3IncidentSupports G D hCan hmax u).Nonempty := hInc
  have hsub : paper11K3IncidentSupports G D hCan hmax u ⊆ SPart G D := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).1
  have hnegative : ∀ w ∈ paper11K3IncidentSupports G D hCan hmax u,
      externalCharge G D w < 0 := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).2.1
  have hrepair : ∀ w ∈ paper11K3IncidentSupports G D hCan hmax u,
      u ∈ paperChosenRepairSet G D hCan hmax w := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have hle := paper9_repair_degree_le_two G hCan hmax hU _ hsub hnegative hrepair
  have hpos : 0 < (paper11K3IncidentSupports G D hCan hmax u).card :=
    Finset.card_pos.mpr hne
  omega
end C6BipartiteDomination
