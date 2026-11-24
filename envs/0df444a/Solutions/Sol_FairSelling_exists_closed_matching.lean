-- Prove2me | solution 1 for FairSelling.exists_closed_matching
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T03:08:55.955659+00:00
-- url     : https://prove2.me/submissions/0f295075-ba2a-4cb6-9d82-948523e57e40

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsMatching
import Theorems.Thm_FairSelling_nbhd_subset
import Theorems.Thm_FairSelling_mem_nbhd_iff

set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {α β : Type*} [DecidableEq α] [DecidableEq β]
namespace FairSelling
theorem _root_.solution [Nonempty β]
    (acc : α → β → Prop) [DecidableRel acc] :
    ∀ (m : ℕ) (A : Finset α) (B : Finset β), A.card = m → A.card ≤ B.card →
    ∃ (K : Finset α) (f : α → β), K ⊆ A ∧ Set.InjOn f K ∧
      (∀ k ∈ K, f k ∈ B) ∧ (∀ k ∈ K, acc k (f k)) ∧
      (∀ a ∈ A, a ∉ K → ∀ k ∈ K, ¬ acc a (f k)) ∧
      (K = A ∨ ∃ b ∈ B, b ∉ K.image f ∧ ∀ a ∈ A, a ∉ K → ¬ acc a b) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro A B hm hcard
    by_cases hall : ∀ X ⊆ A, X.card ≤ (X.biUnion (nbhd B acc)).card
    · -- Hall's condition holds: a perfect matching saturating `A`
      have key : ∀ s : Finset {a // a ∈ A},
          s.card ≤ (s.biUnion (fun a => nbhd B acc a.1)).card := by
        intro s
        have h1 : (s.image (fun a => a.1)).card = s.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have h2 : (s.image (fun a => a.1)) ⊆ A := by
          intro x hx
          simp only [Finset.mem_image] at hx
          obtain ⟨a, _, rfl⟩ := hx
          exact a.2
        have h3 : (s.image (fun a => a.1)).biUnion (nbhd B acc)
            = s.biUnion (fun a => nbhd B acc a.1) := by
          ext b
          simp only [Finset.mem_biUnion, Finset.mem_image]
          constructor
          · rintro ⟨x, ⟨a, ha, rfl⟩, hb⟩; exact ⟨a, ha, hb⟩
          · rintro ⟨a, ha, hb⟩; exact ⟨a.1, ⟨a, ha, rfl⟩, hb⟩
        have := hall _ h2
        rwa [h1, h3] at this
      obtain ⟨f0, hf0inj, hf0mem⟩ :=
        (Finset.all_card_le_biUnion_card_iff_exists_injective
          (fun a : {a // a ∈ A} => nbhd B acc a.1)).mp key
      classical
      refine ⟨A, fun a => if h : a ∈ A then f0 ⟨a, h⟩ else Classical.arbitrary β,
        Finset.Subset.refl _, ?_, ?_, ?_, ?_, Or.inl rfl⟩
      · intro x hx y hy hxy
        simp only [Finset.mem_coe] at hx hy
        simp only [dif_pos hx, dif_pos hy] at hxy
        exact congrArg Subtype.val (hf0inj hxy)
      · intro k hk
        simp only [dif_pos hk]
        exact (mem_nbhd_iff.mp (hf0mem ⟨k, hk⟩)).1
      · intro k hk
        simp only [dif_pos hk]
        exact (mem_nbhd_iff.mp (hf0mem ⟨k, hk⟩)).2
      · intro a ha hna
        exact absurd ha hna
    · -- Hall's condition fails
      push_neg at hall
      obtain ⟨X, hXA, hX⟩ := hall
      have hXne : X.Nonempty := by
        rcases Finset.eq_empty_or_nonempty X with rfl | h
        · simp at hX
        · exact h
      set N : Finset β := X.biUnion (nbhd B acc) with hN
      have hNB : N ⊆ B := by
        intro b hb
        obtain ⟨a, _, hb⟩ := Finset.mem_biUnion.mp hb
        exact nbhd_subset B acc a hb
      have hXcard : 0 < X.card := Finset.card_pos.mpr hXne
      have hA1card : (A \ X).card < A.card := by
        have : (A \ X).card = A.card - X.card := Finset.card_sdiff_of_subset hXA
        have hle : X.card ≤ A.card := Finset.card_le_card hXA
        omega
      have hB1card : (A \ X).card ≤ (B \ N).card := by
        have h1 : (A \ X).card = A.card - X.card := Finset.card_sdiff_of_subset hXA
        have h2 : (B \ N).card = B.card - N.card := Finset.card_sdiff_of_subset hNB
        have hNcard : N.card < X.card := hX
        have hXle : X.card ≤ A.card := Finset.card_le_card hXA
        omega
      obtain ⟨K, f, hKA1, hinj, hfB1, hacc, hclosed, hlast⟩ :=
        IH (A \ X).card (hm ▸ hA1card) (A \ X) (B \ N) rfl hB1card
      have hKA : K ⊆ A := fun a ha => (Finset.mem_sdiff.mp (hKA1 ha)).1
      have hKX : ∀ a ∈ K, a ∉ X := fun a ha => (Finset.mem_sdiff.mp (hKA1 ha)).2
      -- an agent of `X` accepts only parts of `N`
      have hXacc : ∀ a ∈ X, ∀ b ∈ B, acc a b → b ∈ N := by
        intro a ha b hb hab
        exact Finset.mem_biUnion.mpr ⟨a, ha, mem_nbhd_iff.mpr ⟨hb, hab⟩⟩
      have hfB : ∀ k ∈ K, f k ∈ B := fun k hk => (Finset.mem_sdiff.mp (hfB1 k hk)).1
      have hfN : ∀ k ∈ K, f k ∉ N := fun k hk => (Finset.mem_sdiff.mp (hfB1 k hk)).2
      have hclosed' : ∀ a ∈ A, a ∉ K → ∀ k ∈ K, ¬ acc a (f k) := by
        intro a ha hna k hk hacc'
        by_cases hax : a ∈ X
        · exact hfN k hk (hXacc a hax (f k) (hfB k hk) hacc')
        · exact hclosed a (Finset.mem_sdiff.mpr ⟨ha, hax⟩) hna k hk hacc'
      refine ⟨K, f, hKA, hinj, hfB, hacc, hclosed', Or.inr ?_⟩
      rcases hlast with hKeq | ⟨b, hbB1, hbim, hbacc⟩
      · -- every agent outside `X` is matched: pick a part outside `N ∪ f(K)`
        have himcard : (K.image f).card = K.card := Finset.card_image_of_injOn hinj
        have hKcard : K.card = (A \ X).card := by rw [hKeq]
        have hdisj : Disjoint (K.image f) N := by
          refine Finset.disjoint_left.mpr ?_
          intro b hb
          simp only [Finset.mem_image] at hb
          obtain ⟨k, hk, rfl⟩ := hb
          exact hfN k hk
        have hsub : (K.image f) ∪ N ⊆ B := by
          refine Finset.union_subset ?_ hNB
          intro b hb
          simp only [Finset.mem_image] at hb
          obtain ⟨k, hk, rfl⟩ := hb
          exact hfB k hk
        have hcards : ((K.image f) ∪ N).card < B.card := by
          have h1 : ((K.image f) ∪ N).card = (K.image f).card + N.card :=
            Finset.card_union_of_disjoint hdisj
          have h2 : (A \ X).card = A.card - X.card := Finset.card_sdiff_of_subset hXA
          have hXle : X.card ≤ A.card := Finset.card_le_card hXA
          have hNcard : N.card < X.card := hX
          omega
        obtain ⟨b, hbB, hbnot⟩ : ∃ b ∈ B, b ∉ (K.image f) ∪ N := by
          by_contra hcon
          push_neg at hcon
          exact absurd (Finset.card_le_card (fun b hb => hcon b hb)) (not_le.mpr hcards)
        refine ⟨b, hbB, fun hb => hbnot (Finset.mem_union_left _ hb), ?_⟩
        intro a ha hna hacc'
        by_cases hax : a ∈ X
        · exact hbnot (Finset.mem_union_right _ (hXacc a hax b hbB hacc'))
        · exact hna (hKeq ▸ Finset.mem_sdiff.mpr ⟨ha, hax⟩)
      · refine ⟨b, (Finset.mem_sdiff.mp hbB1).1, hbim, ?_⟩
        intro a ha hna hacc'
        by_cases hax : a ∈ X
        · exact (Finset.mem_sdiff.mp hbB1).2
            (hXacc a hax b (Finset.mem_sdiff.mp hbB1).1 hacc')
        · exact hbacc a (Finset.mem_sdiff.mpr ⟨ha, hax⟩) hna hacc'
end FairSelling
