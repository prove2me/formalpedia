-- Prove2me | solution 1 for C6BipartiteDomination.paper11K4_owner_excludes_k3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:08.399002+00:00
-- url     : https://prove2.me/submissions/d2255490-fba6-4079-b9a2-2c5244161f36

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
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
    u ∉ paper11K3RightVertices G D hCan hmax := by
  intro hu3
  have hB : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  obtain ⟨w4, hw4⟩ := (Finset.mem_filter.mp hu).2
  obtain ⟨w3, hw3⟩ := (Finset.mem_filter.mp hu3).2
  have hw4Info := mem_paper11K4Supports G (Finset.mem_filter.mp hw4).1
  have hw3Info := mem_paper11K3Supports G (Finset.mem_filter.mp hw3).1
  have hTcard : (paper11NegativeIncidentSupports G D hCan hmax u).card = 1 := by
    have hw4T : w4 ∈ paper11NegativeIncidentSupports G D hCan hmax u := by
      simp [paper11NegativeIncidentSupports, paper11NegativeSupports,
        hw4Info.1, hw4Info.2.1, (Finset.mem_filter.mp hw4).2]
    exact paper9_repair_degree_eq_one_at_k4 G hCan hmax (w₄ := w4) hB
      (paper11NegativeIncidentSupports G D hCan hmax u)
      (by intro v hv; exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp hv).1).1)
      (by intro v hv; exact (Finset.mem_filter.mp
        (Finset.mem_filter.mp hv).1).2)
      (by intro v hv; exact (Finset.mem_filter.mp hv).2)
      hw4T hw4Info.2.2
  have hmem4 : w4 ∈ paper11NegativeIncidentSupports G D hCan hmax u := by
    simp [paper11NegativeIncidentSupports, paper11NegativeSupports,
      hw4Info.1, hw4Info.2.1, (Finset.mem_filter.mp hw4).2]
  have hmem3 : w3 ∈ paper11NegativeIncidentSupports G D hCan hmax u := by
    simp [paper11NegativeIncidentSupports, paper11NegativeSupports,
      hw3Info.1, hw3Info.2.1, (Finset.mem_filter.mp hw3).2]
  have hEqSet : paper11NegativeIncidentSupports G D hCan hmax u = {w4} := by
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hTcard
    have haw4 : a = w4 := by
      have : w4 ∈ ({a} : Finset V) := by simpa [ha] using hmem4
      exact (Finset.mem_singleton.mp this).symm
    simpa [haw4] using ha
  have hw3eq : w3 = w4 := by
    rw [hEqSet] at hmem3
    exact Finset.mem_singleton.mp hmem3
  have hk3 : kCharge G D w3 = 3 := hw3Info.2.2
  have hk4 : kCharge G D w4 = 4 := hw4Info.2.2
  rw [hw3eq] at hk3
  omega
end C6BipartiteDomination
