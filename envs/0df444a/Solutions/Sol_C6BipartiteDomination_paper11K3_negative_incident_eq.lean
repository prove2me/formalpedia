-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_negative_incident_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:03.126124+00:00
-- url     : https://prove2.me/submissions/896f85ca-6a24-46c5-bcff-2ba04b3e1383

import Definitions.Def_C6BipartiteDomination_PaperSection11
import Definitions.Def_C6BipartiteDomination_PaperSection11_2
import Theorems.Thm_C6BipartiteDomination_paper11K4_owner_excludes_k3
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification


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
    (hu : u ∈ paper11K3RightVertices G D hCan hmax) :
    paper11NegativeIncidentSupports G D hCan hmax u =
      paper11K3IncidentSupports G D hCan hmax u := by
  classical
  apply Finset.ext
  intro w
  constructor
  · intro hw
    have hneg := Finset.mem_filter.mp hw
    have hsup := Finset.mem_filter.mp hneg.1
    have hclass := lemma_7_2_negative_charge_classification G hCan hmax
      hsup.1 hsup.2
    rcases hclass with h3 | h3 | h4
    · simp only [paper11K3IncidentSupports, paper11K3Supports,
        paper11NegativeSupports, Finset.mem_filter]
      exact ⟨⟨⟨hsup.1, hsup.2⟩, h3.1⟩, hneg.2⟩
    · simp only [paper11K3IncidentSupports, paper11K3Supports,
        paper11NegativeSupports, Finset.mem_filter]
      exact ⟨⟨⟨hsup.1, hsup.2⟩, h3.1⟩, hneg.2⟩
    · have hu4 : u ∈ paper11K4RightVertices G D hCan hmax := by
        rw [paper11K4RightVertices]
        simp only [Finset.mem_filter]
        refine ⟨(Finset.mem_filter.mp hu).1, ⟨w, ?_⟩⟩
        simp only [paper11K4IncidentSupports, paper11K4Supports,
          paper11NegativeSupports, Finset.mem_filter]
        exact ⟨⟨⟨hsup.1, hsup.2⟩, h4.1⟩, hneg.2⟩
      exact (paper11K4_owner_excludes_k3 G hCan hmax hu4 hu).elim
  · intro hw
    have hi := Finset.mem_filter.mp hw
    have hs := Finset.mem_filter.mp hi.1
    have hN := Finset.mem_filter.mp hs.1
    simp only [paper11NegativeIncidentSupports, paper11NegativeSupports,
      Finset.mem_filter]
    exact ⟨hN, hi.2⟩
end C6BipartiteDomination
