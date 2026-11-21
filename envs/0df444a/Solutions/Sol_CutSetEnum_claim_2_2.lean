-- Prove2me | solution 1 for CutSetEnum.claim_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:48:41.570369+00:00
-- url     : https://prove2.me/submissions/f3d6402b-e50f-42b8-84f5-dea1a2853bff

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model
import Definitions.Def_CutSetEnum_cutSet
import Definitions.Def_CutSetEnum_IsOptKCutValue
import Definitions.Def_CutSetEnum_IsSourceMinMinTerminalCut
import Definitions.Def_CutSetEnum_Coll
import Definitions.Def_CutSetEnum_IsMinTransversal

open HyperKCut.Structure

namespace Aux_CutSetEnum_claim_2_2

open CutSetEnum

variable {V : Type} [Fintype V] [DecidableEq V]

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

end Aux_CutSetEnum_claim_2_2

open Aux_CutSetEnum_claim_2_2 in
open CutSetEnum in
theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (H : HyperKCut.Structure.Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (U : Finset V) (hU : U.Nonempty) (hUc : Uᶜ.Nonempty)
    (hopt : IsOptKCutValue H k (d H U))
    (S : Finset V) (hS : IsMinTransversal H U S)
    (p : ℕ) (hp : 2 * k ≤ p) (u : Fin p → V) (hu : Function.Injective u)
    (hSu : S = Finset.univ.image u)
    (Hs : Finset V → Finset V)
    (hHs : ∀ X : Finset V, X ⊆ U → X.Nonempty → IsSourceMinMinTerminalCut H X Uᶜ (Hs X)) :
    ∀ i j : Fin p, Hs ((S.erase (u i)).erase (u j)) ⊆ Hs (S.erase (u i)) := by
  intro i j
  have hSU : S ⊆ U := hS.1
  have hcard : S.card = p := by
    rw [hSu, Finset.card_image_of_injective _ hu, Finset.card_univ, Fintype.card_fin]
  have hY : S.erase (u i) ⊆ U := (Finset.erase_subset _ _).trans hSU
  have hX : (S.erase (u i)).erase (u j) ⊆ U := (Finset.erase_subset _ _).trans hY
  have hc1 := Finset.pred_card_le_card_erase (s := S) (a := u i)
  have hc2 := Finset.pred_card_le_card_erase (s := S.erase (u i)) (a := u j)
  have hXne : ((S.erase (u i)).erase (u j)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  have hYne : (S.erase (u i)).Nonempty := by
    rw [← Finset.card_pos]
    omega
  exact mono H ((S.erase (u i)).erase (u j)) (S.erase (u i)) Uᶜ _ _
    (Finset.erase_subset (u j) (S.erase (u i))) (hHs _ hX hXne) (hHs _ hY hYne)
