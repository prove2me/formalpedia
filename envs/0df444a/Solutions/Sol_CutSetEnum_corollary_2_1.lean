-- Prove2me | solution 1 for CutSetEnum.corollary_2_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:41:49.927459+00:00
-- url     : https://prove2.me/submissions/581e007b-e572-487c-a450-4e130eb8f815

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal
set_option autoImplicit false

namespace Aux_CutSetEnum_corollary_2_1

open HyperKCut.Structure CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

theorem cutSet_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    cutSet H Aᶜ = cutSet H A := by
  unfold cutSet
  apply Multiset.filter_congr
  intro e _
  rw [compl_compl]
  exact and_comm

theorem d_eq_card (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H A = (cutSet H A).card := rfl

theorem d_compl (H : HyperKCut.Structure.Hypergraph V) (A : Finset V) :
    d H Aᶜ = d H A := by
  rw [d_eq_card, d_eq_card, cutSet_compl]

/-- the core of Proposition 2.1: any minimum `(S, Uᶜ)`-terminal cut of a transversal -/
theorem min_cut_of_transversal (H : HyperKCut.Structure.Hypergraph V) (U S : Finset V)
    (hSU : S ⊆ U) (hT : IsTransversal H U S) (A : Finset V)
    (hA : IsMinTerminalCut H S Uᶜ A) : cutSet H A = cutSet H U := by
  by_contra hne
  obtain ⟨⟨hSA, hAd⟩, hmin⟩ := hA
  have hdU : d H A ≤ d H U := hmin U ⟨hSU, disjoint_compl_right⟩
  have hAU : A ⊆ U := by
    intro x hx
    by_contra hxU
    exact Finset.disjoint_left.mp hAd hx (Finset.mem_compl.mpr hxU)
  have hmem : Aᶜ ∈ Coll H U := by
    show Uᶜ ⊂ Aᶜ ∧ d H Aᶜ ≤ d H U ∧ cutSet H Aᶜ ≠ cutSet H U
    refine ⟨?_, ?_, ?_⟩
    · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.compl_subset_compl.mpr hAU, ?_⟩
      intro heq
      have : A = U := compl_injective heq.symm
      apply hne
      rw [this]
    · rw [d_compl]
      exact hdU
    · rw [cutSet_compl]
      exact hne
  obtain ⟨x, hx⟩ := hT _ hmem
  rw [Finset.mem_inter, Finset.mem_compl] at hx
  exact hx.2 (hSA hx.1)
lemma meets_of (e X : Finset V) (x : V) (he : x ∈ e) (hX : x ∈ X) : Meets e X :=
  ⟨x, Finset.mem_inter.mpr ⟨he, hX⟩⟩

lemma meets_elim {e X : Finset V} (h : Meets e X) : ∃ x, x ∈ e ∧ x ∈ X := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, Finset.mem_inter.mp hx⟩

lemma comb (P Q R T : Prop) [Decidable P] [Decidable Q] [Decidable R] [Decidable T]
    (h1 : P → R ∨ T) (h2 : Q → R ∨ T) (h3 : P → Q → R ∧ T) :
    ((if P then 1 else 0) + (if Q then 1 else 0) : ℕ) ≤
      (if R then 1 else 0) + (if T then 1 else 0) := by
  split_ifs <;> first | omega | (exfalso; tauto)

lemma edge_sub (e A B : Finset V) :
    ((if Meets e (A ∩ B) ∧ Meets e (A ∩ B)ᶜ then 1 else 0) +
      (if Meets e (A ∪ B) ∧ Meets e (A ∪ B)ᶜ then 1 else 0) : ℕ) ≤
      (if Meets e A ∧ Meets e Aᶜ then 1 else 0) + (if Meets e B ∧ Meets e Bᶜ then 1 else 0) := by
  apply comb
  · rintro ⟨m1, m2⟩
    obtain ⟨x, hxe, hx⟩ := meets_elim m1
    obtain ⟨y, hye, hy⟩ := meets_elim m2
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_compl, Finset.mem_inter] at hy
    by_cases hyA : y ∈ A
    · right
      exact ⟨meets_of e B x hxe hx.2,
        meets_of e Bᶜ y hye (Finset.mem_compl.mpr (fun hyB => hy ⟨hyA, hyB⟩))⟩
    · left
      exact ⟨meets_of e A x hxe hx.1, meets_of e Aᶜ y hye (Finset.mem_compl.mpr hyA)⟩
  · rintro ⟨m1, m2⟩
    obtain ⟨x, hxe, hx⟩ := meets_elim m1
    obtain ⟨z, hze, hz⟩ := meets_elim m2
    rw [Finset.mem_union] at hx
    rw [Finset.mem_compl, Finset.mem_union] at hz
    rcases hx with hxA | hxB
    · left
      exact ⟨meets_of e A x hxe hxA,
        meets_of e Aᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inl h)))⟩
    · right
      exact ⟨meets_of e B x hxe hxB,
        meets_of e Bᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inr h)))⟩
  · rintro ⟨m1, _⟩ ⟨_, m4⟩
    obtain ⟨x, hxe, hx⟩ := meets_elim m1
    obtain ⟨z, hze, hz⟩ := meets_elim m4
    rw [Finset.mem_inter] at hx
    rw [Finset.mem_compl, Finset.mem_union] at hz
    exact ⟨⟨meets_of e A x hxe hx.1,
        meets_of e Aᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inl h)))⟩,
      ⟨meets_of e B x hxe hx.2,
        meets_of e Bᶜ z hze (Finset.mem_compl.mpr (fun h => hz (Or.inr h)))⟩⟩

lemma submod (H : HyperKCut.Structure.Hypergraph V) (A B : Finset V) :
    d H (A ∩ B) + d H (A ∪ B) ≤ d H A + d H B := by
  unfold d
  rw [← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter,
    ← Multiset.countP_eq_card_filter, ← Multiset.countP_eq_card_filter]
  generalize H.edges = s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.countP_cons, Multiset.countP_cons, Multiset.countP_cons,
      Multiset.countP_cons]
    have := edge_sub a A B
    omega

lemma mono (H : HyperKCut.Structure.Hypergraph V) (X Y T A B : Finset V) (hXY : X ⊆ Y)
    (hA : IsSourceMinMinTerminalCut H X T A) (hB : IsSourceMinMinTerminalCut H Y T B) :
    A ⊆ B := by
  obtain ⟨⟨⟨hXA, hAT⟩, hAmin⟩, hAsrc⟩ := hA
  obtain ⟨⟨⟨hYB, hBT⟩, hBmin⟩, _⟩ := hB
  have hsub := submod H A B
  have h1 : d H B ≤ d H (A ∪ B) :=
    hBmin (A ∪ B) ⟨hYB.trans Finset.subset_union_right,
      Finset.disjoint_union_left.mpr ⟨hAT, hBT⟩⟩
  have h2 : IsMinTerminalCut H X T (A ∩ B) := by
    refine ⟨⟨Finset.subset_inter hXA (hXY.trans hYB), hAT.mono_left Finset.inter_subset_left⟩, ?_⟩
    intro U' hU'
    have := hAmin U' hU'
    omega
  exact (hAsrc _ h2).trans Finset.inter_subset_right


theorem term_subset_U {H : HyperKCut.Structure.Hypergraph V} {X U A : Finset V}
    (h : IsTerminalCut X Uᶜ A) : A ⊆ U := by
  intro x hx
  by_contra hxU
  exact Finset.disjoint_left.mp h.2 hx (Finset.mem_compl.mpr hxU)

theorem exists_cross_edge (H : HyperKCut.Structure.Hypergraph V) (U Q : Finset V)
    (hd : d H Q = d H U) (hne : cutSet H Q ≠ cutSet H U) :
    ∃ e ∈ H.edges, (Meets e U ∧ Meets e Uᶜ) ∧ ¬ (Meets e Q ∧ Meets e Qᶜ) := by
  by_contra hcon
  push_neg at hcon
  apply hne
  symm
  have h1 : cutSet H U = H.edges.filter
      (fun e => (Meets e U ∧ Meets e Uᶜ) ∧ (Meets e Q ∧ Meets e Qᶜ)) := by
    unfold cutSet
    apply Multiset.filter_congr
    intro e he
    exact ⟨fun h => ⟨h, hcon e he h⟩, fun h => h.1⟩
  have h2 : cutSet H U ≤ cutSet H Q := by
    rw [h1]
    unfold cutSet
    exact Multiset.monotone_filter_right _ (fun b hb => hb.2)
  apply Multiset.eq_of_le_of_card_le h2
  rw [← d_eq_card, ← d_eq_card, hd]

/-- Claim 2.1 core. -/
theorem claim21_core (H : HyperKCut.Structure.Hypergraph V) (U S X : Finset V) (ui : V)
    (hT : IsTransversal H U S) (hX : X = S.erase ui)
    (hmin : ¬ IsTransversal H U X) (Hh : Finset V)
    (hHh : IsSourceMinMinTerminalCut H X Uᶜ Hh) : Hhᶜ ∈ Coll H U := by
  have hnt := hmin
  unfold IsTransversal at hnt
  push_neg at hnt
  obtain ⟨Q, hQ, hQX⟩ := hnt
  obtain ⟨hUQ, hdQ, hcQ⟩ := hQ
  have hXA : X ⊆ Qᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hxQ
    have : x ∈ X ∩ Q := Finset.mem_inter.mpr ⟨hx, hxQ⟩
    rw [hQX] at this
    simp at this
  have hAd : Disjoint Qᶜ Uᶜ := by
    rw [Finset.disjoint_left]
    intro x hx hxU
    exact (Finset.mem_compl.mp hx) (hUQ.1 hxU)
  obtain ⟨⟨⟨hXH, hHd⟩, hHmin⟩, hHsrc⟩ := hHh
  have hHU : Hh ⊆ U := term_subset_U (H := H) ⟨hXH, hHd⟩
  have h1 : d H Hh ≤ d H Qᶜ := hHmin _ ⟨hXA, hAd⟩
  rw [d_compl] at h1
  -- the cut sets differ
  have hcut : cutSet H Hhᶜ ≠ cutSet H U := by
    rw [cutSet_compl]
    by_cases hlt : d H Hh < d H U
    · intro h
      have : d H Hh = d H U := by rw [d_eq_card, d_eq_card, h]
      omega
    · have hdH : d H Hh = d H U := by omega
      have hs := submod H Hh Qᶜ
      have hi : d H Hh ≤ d H (Hh ∩ Qᶜ) := hHmin _
        ⟨Finset.subset_inter hXH hXA, hHd.mono_left Finset.inter_subset_left⟩
      have hu : d H Hh ≤ d H (Hh ∪ Qᶜ) := hHmin _
        ⟨hXH.trans Finset.subset_union_left, Finset.disjoint_union_left.mpr ⟨hHd, hAd⟩⟩
      rw [d_compl] at hs
      have hmin2 : IsMinTerminalCut H X Uᶜ (Hh ∩ Qᶜ) := by
        refine ⟨⟨Finset.subset_inter hXH hXA, hHd.mono_left Finset.inter_subset_left⟩, ?_⟩
        intro U' hU'
        have := hHmin U' hU'
        omega
      have hsubA : Hh ⊆ Qᶜ := (hHsrc _ hmin2).trans Finset.inter_subset_right
      have hdQU : d H Q = d H U := by omega
      obtain ⟨e, he, ⟨heU, heUc⟩, heQ⟩ := exists_cross_edge H U Q hdQU hcQ
      have hmQ : Meets e Q := by
        obtain ⟨x, hx⟩ := heUc
        rw [Finset.mem_inter] at hx
        exact ⟨x, Finset.mem_inter.mpr ⟨hx.1, hUQ.1 hx.2⟩⟩
      have hnQc : ¬ Meets e Qᶜ := fun h => heQ ⟨hmQ, h⟩
      have hnH : ¬ Meets e Hh := by
        intro h
        obtain ⟨x, hx⟩ := h
        rw [Finset.mem_inter] at hx
        exact hnQc ⟨x, Finset.mem_inter.mpr ⟨hx.1, hsubA hx.2⟩⟩
      intro h
      have hmem : e ∈ cutSet H U := by
        unfold cutSet
        rw [Multiset.mem_filter]
        exact ⟨he, heU, heUc⟩
      rw [← h] at hmem
      unfold cutSet at hmem
      rw [Multiset.mem_filter] at hmem
      exact hnH hmem.2.1
  show Uᶜ ⊂ Hhᶜ ∧ d H Hhᶜ ≤ d H U ∧ cutSet H Hhᶜ ≠ cutSet H U
  refine ⟨?_, ?_, hcut⟩
  · refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.compl_subset_compl.mpr hHU, ?_⟩
    intro heq
    have : Hh = U := compl_injective heq.symm
    apply hcut
    rw [this, cutSet_compl]
  · rw [d_compl]
    omega

theorem claim21_full (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X))
    (i : Fin p) : (Hs (S.erase (u i)))ᶜ ∈ Coll H U ∧ u i ∈ (Hs (S.erase (u i)))ᶜ := by
  have hSU : S ⊆ U := hS.1
  have hcard : S.card = p := by
    rw [hSu, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  have hui : u i ∈ S := by rw [hSu]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hY : S.erase (u i) ⊆ U := (Finset.erase_subset _ _).trans hSU
  have hc1 := Finset.pred_card_le_card_erase (s := S) (a := u i)
  have hYne : (S.erase (u i)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hmin : ¬ IsTransversal H U (S.erase (u i)) := hS.2.2 _ (Finset.erase_ssubset hui)
  have hHh := hHs _ hY hYne
  have hC := claim21_core H U S (S.erase (u i)) (u i) hS.2.1 rfl hmin _ hHh
  refine ⟨hC, ?_⟩
  obtain ⟨x, hx⟩ := hS.2.1 _ hC
  rw [Finset.mem_inter] at hx
  by_cases hxi : x = u i
  · rw [hxi] at hx
    exact hx.2
  · exfalso
    have hxS : x ∈ S.erase (u i) := Finset.mem_erase.mpr ⟨hxi, hx.1⟩
    exact (Finset.mem_compl.mp hx.2) (hHh.1.1.1 hxS)


end Aux_CutSetEnum_corollary_2_1


open HyperKCut.Structure CutSetEnum Aux_CutSetEnum_corollary_2_1 in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X)) :
    ∀ i : Fin p, u i ∈ (Hs (S.erase (u i)))ᶜ := by
  intro i
  exact (claim21_full H k hk U S hS p hp u hu hSu Hs hHs i).2
