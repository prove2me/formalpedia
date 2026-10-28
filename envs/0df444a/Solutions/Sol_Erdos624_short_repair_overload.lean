-- Prove2me | solution 1 for Erdos624.short_repair_overload
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:29:58.985214+00:00
-- url     : https://prove2.me/submissions/5da58da3-4b08-49cf-aa30-e368ae77eab7

import Mathlib
open Finset

namespace E624R15P
open Finset

theorem overload {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (k s t : ℕ)
    (hts : t ≤ s) (E : Finset C)
    (hE : ∀ u ∈ E, u ∉ L ∅ ∧
      (∀ P ⊆ Z, #Z ≤ #P + s → ∀ a ∈ Icc 1 k,
        ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a → u ∉ L A) ∧
      ∃ a ∈ Icc 1 k, ∃ G ⊆ Z.powerset, (∀ A ∈ G, u ∈ L A) ∧
        (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) ∧
        ∃ T ⊆ Z, #T ≤ t ∧ ∀ A ∈ G, 3 ≤ #A → #A ≠ a → ∃ x ∈ A, x ∈ T) :
    #E * (s - t + 1) ≤ #Z * (#Z + 1) := by
  classical
  set short := Z.powersetCard 1 ∪ Z.powersetCard 2 with hshort
  set Sh := fun u => short.filter (fun A => u ∈ L A) with hSh
  have hmany : ∀ u ∈ E, s - t + 1 ≤ #(Sh u) := by
    intro u hu
    obtain ⟨hbot, hM, a, ha, G, hGZ, hGu, hGcov, T, hTZ, hTc, hT⟩ := hE u hu
    by_contra hlt
    push_neg at hlt
    set S := G.filter (fun A => (#A = 1 ∨ #A = 2) ∧ #A ≠ a) with hS
    have hSsub : S ⊆ Sh u := by
      intro A hA
      rw [hS, mem_filter] at hA
      have hAZ : A ⊆ Z := mem_powerset.1 (hGZ hA.1)
      rw [hSh, mem_filter, hshort, mem_union, mem_powersetCard, mem_powersetCard]
      refine ⟨?_, hGu A hA.1⟩
      rcases hA.2.1 with h | h
      · exact Or.inl ⟨hAZ, h⟩
      · exact Or.inr ⟨hAZ, h⟩
    have hSc : #S ≤ s - t := by have := card_le_card hSsub; omega
    have hne : ∀ A : ↥S, ∃ x, x ∈ (A : Finset U) := by
      intro A
      obtain ⟨-, h1, -⟩ := mem_filter.1
        (show (A : Finset U) ∈ G.filter (fun A => (#A = 1 ∨ #A = 2) ∧ #A ≠ a) from A.2)
      have : 0 < #(A : Finset U) := by omega
      exact card_pos.1 this
    choose pt hpt using hne
    set D := (univ : Finset ↥S).image pt with hD
    have hDc : #D ≤ s - t := card_image_le.trans (by rw [card_univ, Fintype.card_coe]; exact hSc)
    set P := Z \ (D ∪ T) with hP
    have hPc : #Z ≤ #P + s := by
      have h1 := le_card_sdiff (D ∪ T) Z
      have h2 := card_union_le D T
      rw [← hP] at h1
      omega
    obtain ⟨Y, hYP, hYk, hY⟩ := hM P sdiff_subset hPc a ha
    have hYZ : Y ⊆ Z := hYP.trans sdiff_subset
    obtain ⟨A, hAG, hAY⟩ := hGcov Y hYZ hYk
    have huA := hGu A hAG
    have hAP : ∀ x ∈ A, x ∉ D ∧ x ∉ T := by
      intro x hx
      have := hYP (hAY hx)
      rw [hP, mem_sdiff, mem_union] at this
      exact not_or.1 this.2
    by_cases hAa : #A = a
    · exact hY A hAY hAa huA
    · by_cases h3 : 3 ≤ #A
      · obtain ⟨x, hxA, hxT⟩ := hT A hAG h3 hAa
        exact (hAP x hxA).2 hxT
      · have hA0 : A ≠ ∅ := fun h => hbot (h ▸ huA)
        have hpos : 0 < #A := card_pos.2 (nonempty_iff_ne_empty.2 hA0)
        have hAS : A ∈ S := by
          rw [hS, mem_filter]; exact ⟨hAG, by omega, hAa⟩
        exact (hAP (pt ⟨A, hAS⟩) (hpt ⟨A, hAS⟩)).1 (mem_image_of_mem pt (mem_univ _))
  have hsum : #E * (s - t + 1) ≤ ∑ u ∈ E, #(Sh u) := by
    calc #E * (s - t + 1) = ∑ _u ∈ E, (s - t + 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ _ := sum_le_sum hmany
  have hswap : ∑ u ∈ E, #(Sh u) = ∑ A ∈ short, #(E.filter (fun u => u ∈ L A)) := by
    simp only [hSh, card_filter]; rw [sum_comm]
  have hcap : ∑ A ∈ short, #(E.filter (fun u => u ∈ L A)) ≤ 2 * #short := by
    calc _ ≤ ∑ _A ∈ short, 2 := sum_le_sum fun A _ =>
            (card_le_card (fun u hu => (mem_filter.1 hu).2)).trans (hb A)
      _ = 2 * #short := by rw [sum_const, smul_eq_mul, mul_comm]
  have hshc : #short = #Z + (#Z).choose 2 := by
    rw [hshort, card_union_of_disjoint, card_powersetCard, card_powersetCard, Nat.choose_one_right]
    rw [disjoint_left]; intro A h1 h2
    rw [mem_powersetCard] at h1 h2; omega
  have h2 := Nat.choose_succ_right_eq (#Z) 1
  rw [Nat.choose_one_right] at h2
  have h3 : 2 * #short = #Z * (#Z + 1) := by
    rw [hshc]
    rcases Nat.eq_zero_or_pos (#Z) with h | h
    · rw [h]; simp
    · have : #Z * (#Z - 1) + 2 * #Z = #Z * (#Z + 1) := by
        obtain ⟨n, hn⟩ : ∃ n, #Z = n + 1 := ⟨#Z - 1, by omega⟩
        rw [hn]; simp; ring
      linarith
  omega
end E624R15P

namespace Erdos624

theorem short_repair_overload {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (k s t : ℕ)
    (hts : t ≤ s) (E : Finset C)
    (hE : ∀ u ∈ E, u ∉ L ∅ ∧
      (∀ P ⊆ Z, #Z ≤ #P + s → ∀ a ∈ Icc 1 k,
        ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a → u ∉ L A) ∧
      ∃ a ∈ Icc 1 k, ∃ G ⊆ Z.powerset, (∀ A ∈ G, u ∈ L A) ∧
        (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) ∧
        ∃ T ⊆ Z, #T ≤ t ∧ ∀ A ∈ G, 3 ≤ #A → #A ≠ a → ∃ x ∈ A, x ∈ T) :
    #E * (s - t + 1) ≤ #Z * (#Z + 1) := by
  exact E624R15P.overload L hb Z k s t hts E hE

end Erdos624

open Finset

theorem solution {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (Z : Finset U) (k s t : ℕ)
    (hts : t ≤ s) (E : Finset C)
    (hE : ∀ u ∈ E, u ∉ L ∅ ∧
      (∀ P ⊆ Z, #Z ≤ #P + s → ∀ a ∈ Icc 1 k,
        ∃ Y ⊆ P, #Y = k ∧ ∀ A ⊆ Y, #A = a → u ∉ L A) ∧
      ∃ a ∈ Icc 1 k, ∃ G ⊆ Z.powerset, (∀ A ∈ G, u ∈ L A) ∧
        (∀ Y ⊆ Z, #Y = k → ∃ A ∈ G, A ⊆ Y) ∧
        ∃ T ⊆ Z, #T ≤ t ∧ ∀ A ∈ G, 3 ≤ #A → #A ≠ a → ∃ x ∈ A, x ∈ T) :
    #E * (s - t + 1) ≤ #Z * (#Z + 1) :=
  Erdos624.short_repair_overload L hb Z k s t hts E hE
