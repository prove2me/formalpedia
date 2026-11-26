-- Prove2me | solution 1 for C6BipartiteDomination.paper9_lemma_9_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T22:07:15.026472+00:00
-- url     : https://prove2.me/submissions/98812d88-0872-4783-9a3e-babddf8da3f2

import Definitions.Def_C6BipartiteDomination_A9
import Definitions.Def_C6BipartiteDomination_PaperSection9
import Theorems.Thm_C6BipartiteDomination_paperChosenRepairSet_legal
import Theorems.Thm_C6BipartiteDomination_paper9_sCharge_add_xCharge_le_three
import Theorems.Thm_C6BipartiteDomination_paper9_shared_compensation_profile
import Theorems.Thm_C6BipartiteDomination_paper9_shared_set_incidence
import Theorems.Thm_C6BipartiteDomination_paper9_shared_beta_eq_one
import Theorems.Thm_C6BipartiteDomination_paper9_shared_external_charge_eq_four
import Theorems.Thm_C6BipartiteDomination_paper9_union_resource_bound
import Theorems.Thm_C6BipartiteDomination_paper9_unique_extra_S_neighbor
import Theorems.Thm_C6BipartiteDomination_paper9_shared_support_witness_agrees
import Theorems.Thm_C6BipartiteDomination_paper9_repair_degree_eq_one_at_k4
import Theorems.Thm_C6BipartiteDomination_Z0_disjoint_B
import Theorems.Thm_C6BipartiteDomination_lemma_7_2_negative_charge_classification
import Theorems.Thm_C6BipartiteDomination_lemma_8_5_compensation_lower_bound
import Theorems.Thm_C6BipartiteDomination_mem_supportX


set_option autoImplicit true
open C6BipartiteDomination
open Finset BigOperators
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
namespace C6BipartiteDomination
theorem _root_.solution
    {D : Finset V} (hCan : CanonicalTwoLevelOptimum G D)
    (hmax : ∀ v, degreeTo G Finset.univ v ≤ 6)
    {u : V} (huB : u ∈ BPart G D) (T : Finset V)
    (hTsub : T ⊆ SPart G D)
    (hTnegative : ∀ w ∈ T, externalCharge G D w < 0)
    (hTrepair : ∀ w ∈ T,
      u ∈ paperChosenRepairSet G D hCan hmax w)
    (hTcard : T.card = 2) :
    (∀ w ∈ T, kCharge G D w = 3) ∧
      ((xCharge G D u = 1 ∧ sCharge G D u = 2 ∧
          vertexCharge G D u = 11 ∧
          ∀ w ∈ T, sharedCompensation G D (supportX G D w) u = ∅) ∨
       (xCharge G D u = 0 ∧ sCharge G D u = 3 ∧
          vertexCharge G D u = 0 ∧
          ∃ q z, (∀ w ∈ T,
              sharedCompensation G D (supportX G D w) u = {q}) ∧
            q ∈ SPart G D ∧ betaCharge G D q = 1 ∧
            kCharge G D q = 1 ∧ externalCharge G D q = 4 ∧
            z ∈ Z0Part G D ∧ neighborhoodIn G D q = {u, z} ∧
            ∀ w ∈ T, z ∈ supportX G D w)) := by
  classical
  let L : V → Finset V := fun w =>
    sharedCompensation G D (supportX G D w) u
  have hTadj : ∀ w ∈ T, G.Adj w u := by
    intro w hw
    have hLegal := paperChosenRepairSet_legal G hCan hmax
      (hTsub hw) (hTnegative w hw) u (hTrepair w hw)
    exact hLegal.2.1
  have hTneighbors : T ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨hTsub hw, (hTadj w hw).symm⟩
  have hTleS : T.card ≤ sCharge G D u := by
    have hcard := Finset.card_le_card hTneighbors
    simpa [sCharge, degreeTo] using hcard
  have hbudget := paper9_sCharge_add_xCharge_le_three G hCan hmax huB
  have hsle : sCharge G D u ≤ 3 := by omega
  have hxle : xCharge G D u ≤ 1 := by rw [hTcard] at hTleS; omega
  have hThigh : ∀ w ∈ T, 2 ≤ kCharge G D w := by
    intro w hw
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h <;> omega
  have hTclass : ∀ w ∈ T,
      kCharge G D w = 3 ∧
        (betaCharge G D w = 2 ∨ betaCharge G D w = 3) := by
    intro w hw
    have hk4 : kCharge G D w ≠ 4 := by
      intro hk
      have hone := paper9_repair_degree_eq_one_at_k4 G hCan hmax huB T
        hTsub hTnegative hTrepair hw hk
      rw [hTcard] at hone
      omega
    rcases lemma_7_2_negative_charge_classification G hCan hmax
        (hTsub hw) (hTnegative w hw) with h | h | h
    · exact ⟨h.1, Or.inl h.2⟩
    · exact ⟨h.1, Or.inr h.2⟩
    · exact False.elim (hk4 h.1)
  have hLsub : ∀ w ∈ T, L w ⊆ (SPart G D).filter (fun q => G.Adj u q) := by
    intro w hw
    have hX : supportX G D w ⊆ Z0Part G D := by
      intro z hz
      exact (mem_supportX G D w z).mp hz |>.1
    simpa [L] using (paper9_shared_set_incidence G hX huB).1
  have hLdisj : ∀ w ∈ T, Disjoint T (L w) := by
    intro w hw
    have hX : supportX G D w ⊆ Z0Part G D := by
      intro z hz
      exact (mem_supportX G D w z).mp hz |>.1
    simpa [L] using (paper9_shared_set_incidence G hX huB).2 T hThigh
  have hLbound : ∀ w ∈ T, kCharge G D w - 2 ≤ xCharge G D u + (L w).card := by
    intro w hw
    have hChosen : ChosenRepairRelation G D w
        (paperChosenRepairSet G D hCan hmax w) u :=
      ⟨hTrepair w hw,
        paperChosenRepairSet_legal G hCan hmax (hTsub hw)
          (hTnegative w hw) u (hTrepair w hw)⟩
    have h := lemma_8_5_compensation_lower_bound G hCan hmax
      (hTsub hw) (hTnegative w hw) hChosen
    simpa [L] using h
  have hTpositive : 0 < T.card := by omega
  obtain ⟨w₀, hw₀⟩ := Finset.card_pos.mp hTpositive
  by_cases hx1 : xCharge G D u = 1
  · have hs2 : sCharge G D u = 2 := by rw [hTcard] at hTleS; omega
    have hLempty : ∀ w ∈ T, L w = ∅ := by
      intro w hw
      have hle := paper9_union_resource_bound G hTneighbors (hLsub w hw)
        (hLdisj w hw)
      rw [hTcard, hs2] at hle
      have hzero : (L w).card = 0 := by omega
      exact Finset.card_eq_zero.mp hzero
    have hvertex : vertexCharge G D u = 11 := by
      unfold vertexCharge
      rw [hx1, hs2]
      norm_num
    exact ⟨(fun w hw => (hTclass w hw).1), Or.inl ⟨hx1, hs2, hvertex, hLempty⟩⟩
  · have hx0 : xCharge G D u = 0 := by omega
    have hLpositive : ∀ w ∈ T, 1 ≤ (L w).card := by
      intro w hw
      have h := hLbound w hw
      rw [(hTclass w hw).1, hx0] at h
      omega
    have hX₀ : supportX G D w₀ ⊆ Z0Part G D := by
      intro z hz
      exact (mem_supportX G D w₀ z).mp hz |>.1
    have hL₀pos : 0 < (L w₀).card := by
      have := hLpositive w₀ hw₀
      omega
    obtain ⟨q, hqL₀⟩ := Finset.card_pos.mp hL₀pos
    have hqN : q ∈ (SPart G D).filter (fun v => G.Adj u v) := hLsub w₀ hw₀ hqL₀
    have hqNotT : q ∉ T := by
      intro hqT
      exact (Finset.disjoint_left.mp (hLdisj w₀ hw₀) hqT hqL₀).elim
    have hqProfile := paper9_shared_compensation_profile G hX₀ huB hqL₀
    have hqCharge := paper9_shared_external_charge_eq_four G hX₀ huB hqL₀
    have hs3 : sCharge G D u = 3 := by
      have hle := paper9_union_resource_bound G hTneighbors
        (hLsub w₀ hw₀) (hLdisj w₀ hw₀)
      rw [hTcard] at hle
      have hLone : (L w₀).card = 1 := by
        have hpos := hLpositive w₀ hw₀
        omega
      rw [hLone] at hle
      omega
    have hvertex : vertexCharge G D u = 0 := by
      unfold vertexCharge
      rw [hx0, hs3]
      norm_num
    have hqInAll : ∀ w ∈ T, q ∈ L w := by
      intro w hw
      have hpos := hLpositive w hw
      obtain ⟨r, hrL⟩ := Finset.card_pos.mp (by omega : 0 < (L w).card)
      have hrN := hLsub w hw hrL
      have hrNotT : r ∉ T := by
        intro hrT
        exact (Finset.disjoint_left.mp (hLdisj w hw) hrT hrL).elim
      have hqr := paper9_unique_extra_S_neighbor G hTneighbors hTcard hqN hrN
        hqNotT hrNotT hsle
      simpa [hqr] using hrL
    have hLeq : ∀ w ∈ T, L w = {q} := by
      intro w hw
      have hqW := hqInAll w hw
      apply Finset.ext
      intro r
      constructor
      · intro hr
        have hrNotT : r ∉ T := by
          intro hrT
          exact (Finset.disjoint_left.mp (hLdisj w hw) hrT hr).elim
        have hrN := hLsub w hw hr
        have hqr := paper9_unique_extra_S_neighbor G hTneighbors hTcard hqN hrN
          hqNotT hrNotT hsle
        simp [hqr]
      · intro hr
        have hrEq : r = q := Finset.mem_singleton.mp hr
        simpa [hrEq] using hqW
    have hwitness : ∀ w ∈ T, ∃ z, z ∈ Z0Part G D ∧
        z ∈ supportX G D w ∧ neighborhoodIn G D q = {u, z} := by
      intro w hw
      have hX : supportX G D w ⊆ Z0Part G D := by
        intro z hz
        exact (mem_supportX G D w z).mp hz |>.1
      have hqW : q ∈ L w := hqInAll w hw
      obtain ⟨z, hzSupport, hzY, hN⟩ := paper9_shared_support_witness_agrees
        (G := G) huB hX₀ hX hqL₀ hqW
      exact ⟨z, (mem_supportX G D w z).mp hzY |>.1, hzY, hN⟩
    obtain ⟨z, hzZ0, hzSupport₀, hN⟩ := hwitness w₀ hw₀
    have hzSupportAll : ∀ w ∈ T, z ∈ supportX G D w := by
      intro w hw
      obtain ⟨z', hzZ0', hzSupport', hN'⟩ := hwitness w hw
      have hzNeU : z ≠ u := by
        intro hEq
        subst z
        exact (Finset.disjoint_left.mp (Z0_disjoint_B G) hzZ0 huB).elim
      have hpair : z ∈ ({u, z'} : Finset V) := by rw [← hN']; rw [hN]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
      rcases hpair with hzu | hzz
      · exact False.elim (hzNeU hzu)
      · simpa [hzz] using hzSupport'
    have hqBeta := paper9_shared_beta_eq_one G hX₀ huB hqL₀
    exact ⟨(fun w hw => (hTclass w hw).1), Or.inr
      ⟨hx0, hs3, hvertex, q, z, hLeq, hqProfile.1, hqBeta,
        hqProfile.2.2, hqCharge, hzZ0, hN, hzSupportAll⟩⟩
end C6BipartiteDomination
