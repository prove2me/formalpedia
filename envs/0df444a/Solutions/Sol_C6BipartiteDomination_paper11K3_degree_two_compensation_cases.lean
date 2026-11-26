-- Prove2me | solution 1 for C6BipartiteDomination.paper11K3_degree_two_compensation_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:08:14.450676+00:00
-- url     : https://prove2.me/submissions/76059242-4374-42ff-b124-14522351dc13

import Definitions.Def_C6BipartiteDomination_PaperSection10
import Definitions.Def_C6BipartiteDomination_PaperSection11
import Theorems.Thm_C6BipartiteDomination_mem_paper11K3Supports
import Theorems.Thm_C6BipartiteDomination_paper11K3_right_degree_eq_incident_card
import Theorems.Thm_C6BipartiteDomination_paper11_card_two_distinct_members
import Theorems.Thm_C6BipartiteDomination_mem_paper10SpecialQSet
import Theorems.Thm_C6BipartiteDomination_paper9_lemma_9_2


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
      (paper11K3Supports G D) u = 2) :
    (xCharge G D u = 1 ∧ vertexCharge G D u = 11 ∧
      paper11K3Compensation G D hCan hmax u = ∅) ∨
    (xCharge G D u = 0 ∧ vertexCharge G D u = 0 ∧
      ∃ q, paper11K3Compensation G D hCan hmax u = {q} ∧
        externalCharge G D q = 4 ∧
        q ∈ paper10SpecialQSet G hCan hmax ∧
        ∃ data : Paper10SpecialWitness G hCan hmax q, data.u = u) := by
  classical
  have hTcard : (paper11K3IncidentSupports G D hCan hmax u).card = 2 := by
    have := paper11K3_right_degree_eq_incident_card G hCan hmax (u := u)
    rw [this] at hdeg
    exact hdeg
  let T := paper11K3IncidentSupports G D hCan hmax u
  have huB : u ∈ BPart G D := (Finset.mem_filter.mp hu).1
  have hTsub : T ⊆ SPart G D := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).1
  have hTnegative : ∀ w ∈ T, externalCharge G D w < 0 := by
    intro w hw
    exact (mem_paper11K3Supports G (Finset.mem_filter.mp hw).1).2.1
  have hTrepair : ∀ w ∈ T, u ∈ paperChosenRepairSet G D hCan hmax w := by
    intro w hw
    exact (Finset.mem_filter.mp hw).2
  have h9 := paper9_lemma_9_2 G hCan hmax huB T hTsub hTnegative
    hTrepair hTcard
  rcases h9.2 with hcase | hcase
  · rcases hcase with ⟨hx, hs, hcharge, hempty⟩
    have hUnion : paper11K3Compensation G D hCan hmax u = ∅ := by
      ext q
      simp only [paper11K3Compensation, Finset.mem_biUnion]
      constructor
      · rintro ⟨w, hw, hq⟩
        rw [hempty w hw] at hq
        simp at hq
      · intro hq
        simp at hq
    exact Or.inl ⟨hx, hcharge, hUnion⟩
  · rcases hcase with ⟨hx, hs, hcharge, q, z, hcomp, hqS, hqβ,
      hqk, hqCharge, hz0, hqN, hzAll⟩
    obtain ⟨w₁, w₂, hne, hw₁, hw₂⟩ :=
      paper11_card_two_distinct_members hTcard
    have hUnion : paper11K3Compensation G D hCan hmax u = {q} := by
      ext r
      simp only [paper11K3Compensation, Finset.mem_biUnion]
      constructor
      · rintro ⟨w, hw, hr⟩
        rw [hcomp w hw] at hr
        exact hr
      · intro hr
        have hrq : r = q := Finset.mem_singleton.mp hr
        subst r
        refine ⟨w₁, hw₁, ?_⟩
        rw [hcomp w₁ hw₁]
        simp
    have hw₁Info := mem_paper11K3Supports G (Finset.mem_filter.mp hw₁).1
    have hw₂Info := mem_paper11K3Supports G (Finset.mem_filter.mp hw₂).1
    let hdata : Paper10SpecialWitness G hCan hmax q := {
      u := u
      w₁ := w₁
      w₂ := w₂
      z := z
      w_ne := hne
      w₁S := hw₁Info.1
      w₂S := hw₂Info.1
      w₁negative := hw₁Info.2.1
      w₂negative := hw₂Info.2.1
      uB := huB
      repair₁ := (Finset.mem_filter.mp hw₁).2
      repair₂ := (Finset.mem_filter.mp hw₂).2
      qShared₁ := by rw [hcomp w₁ hw₁]; simp
      qShared₂ := by rw [hcomp w₂ hw₂]; simp
      zSupport₁ := hzAll w₁ hw₁
      zSupport₂ := hzAll w₂ hw₂
      qNeighborhood := hqN
    }
    have hqQ : q ∈ paper10SpecialQSet G hCan hmax :=
      (mem_paper10SpecialQSet G hCan hmax q).mpr ⟨hdata⟩
    exact Or.inr ⟨hx, hcharge, q, hUnion, hqCharge, hqQ, hdata, by rfl⟩
end C6BipartiteDomination
