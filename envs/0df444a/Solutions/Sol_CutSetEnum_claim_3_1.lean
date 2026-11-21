-- Prove2me | solution 1 for CutSetEnum.claim_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-21T02:48:39.901283+00:00
-- url     : https://prove2.me/submissions/ce792ed7-6e5f-4d99-b948-9c16cee61d90

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut
set_option autoImplicit false

namespace Aux_CutSetEnum_claim_3_1

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


theorem exists_min_cut (H : HyperKCut.Structure.Hypergraph V) (S T U0 : Finset V)
    (h0 : IsTerminalCut S T U0) : ∃ A, IsMinTerminalCut H S T A := by
  classical
  have hne : (Finset.univ.filter (fun A : Finset V => IsTerminalCut S T A)).Nonempty :=
    ⟨U0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (fun A => d H A) hne
  refine ⟨A, (Finset.mem_filter.mp hA).2, fun U' hU' => hmin U' ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hU'⟩

theorem rec_min (H : HyperKCut.Structure.Hypergraph V) (S T U : Finset V)
    (hU : IsTerminalCut S T U)
    (hrec : ∀ A : Finset V, IsMinTerminalCut H S T A → cutSet H A = cutSet H U) :
    ∀ U', IsTerminalCut S T U' → d H U ≤ d H U' := by
  obtain ⟨A, hA⟩ := exists_min_cut H S T U hU
  have h := hrec A hA
  have hdA : d H A = d H U := by rw [d_eq_card, d_eq_card, h]
  intro U' hU'
  rw [← hdA]
  exact hA.2 U' hU'


end Aux_CutSetEnum_claim_3_1


open HyperKCut.Structure CutSetEnum Aux_CutSetEnum_claim_3_1 in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S T : Finset V)
    (hSU : S ⊆ U) (hSne : S.Nonempty) (hScard : S.card ≤ 2 * k - 1)
    (hSrec : ∀ A : Finset V, IsMinTerminalCut H S Uᶜ A → cutSet H A = cutSet H U)
    (hTU : T ⊆ Uᶜ) (hTne : T.Nonempty) (hTcard : T.card ≤ 2 * k - 1)
    (hTrec : ∀ A : Finset V, IsMinTerminalCut H U T A → cutSet H A = cutSet H U)
    (Y : Finset V) (hY : IsSourceMinMinTerminalCut H S T Y) :
    cutSet H Y = cutSet H U := by
  have hUT : Disjoint U T := by
    rw [Finset.disjoint_left]
    intro x hx hxT
    exact (Finset.mem_compl.mp (hTU hxT)) hx
  have hminS := rec_min H S Uᶜ U ⟨hSU, disjoint_compl_right⟩ hSrec
  have hminT := rec_min H U T U ⟨subset_refl _, hUT⟩ hTrec
  obtain ⟨⟨⟨hSY, hYT⟩, hYmin⟩, hYsrc⟩ := hY
  have h1 : d H Y ≤ d H U := hYmin U ⟨hSU, hUT⟩
  have h2 : d H U ≤ d H (U ∩ Y) :=
    hminS _ ⟨Finset.subset_inter hSU hSY, disjoint_compl_right.mono_left Finset.inter_subset_left⟩
  have h3 : d H U ≤ d H (U ∪ Y) :=
    hminT _ ⟨Finset.subset_union_left, Finset.disjoint_union_left.mpr ⟨hUT, hYT⟩⟩
  have hs := submod H U Y
  have hmin2 : IsMinTerminalCut H S T (U ∩ Y) := by
    refine ⟨⟨Finset.subset_inter hSU hSY, hYT.mono_left Finset.inter_subset_right⟩, ?_⟩
    intro U' hU'
    have := hYmin U' hU'
    omega
  have hYU : Y ⊆ U := (hYsrc _ hmin2).trans Finset.inter_subset_left
  apply hSrec
  refine ⟨⟨hSY, ?_⟩, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hx hxU
    exact (Finset.mem_compl.mp hxU) (hYU hx)
  · intro U' hU'
    have := hminS U' hU'
    omega
