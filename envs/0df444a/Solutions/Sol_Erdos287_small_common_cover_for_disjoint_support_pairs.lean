-- Prove2me | solution 1 for Erdos287.small_common_cover_for_disjoint_support_pairs
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:48:18.277776+00:00
-- url     : https://prove2.me/submissions/aa03f2f7-9073-454a-ba78-4e9a7064c930

import Mathlib

open Finset

set_option autoImplicit false

private theorem failed_subsets {α : Type*} [DecidableEq α] (U A B : Finset α) (k : ℕ)
    (hA : A ⊆ U) (hB : B ⊆ U) (hAB : Disjoint A B)
    (hsize : A.card + B.card ≤ k) :
    (U.powerset.filter (fun C => ¬ (A ⊆ C ∧ Disjoint B C))).card ≤
      2 ^ U.card - 2 ^ (U.card - k) := by
  classical
  let free := U \ (A ∪ B)
  let good := U.powerset.filter (fun C => A ⊆ C ∧ Disjoint B C)
  have hfree (C : Finset α) (hC : C ∈ free.powerset) {x : α} (hx : x ∈ C) :
      x ∈ U ∧ x ∉ A ∧ x ∉ B := by
    obtain ⟨hU, hnot⟩ := mem_sdiff.mp (mem_powerset.mp hC hx)
    exact ⟨hU, fun ha => hnot (mem_union_left _ ha), fun hb => hnot (mem_union_right _ hb)⟩
  have hdis (C : Finset α) (hC : C ∈ free.powerset) : Disjoint A C :=
    disjoint_left.mpr fun x hxA hxC => (hfree C hC hxC).2.1 hxA
  have hgood : free.powerset.card ≤ good.card := by
    apply card_le_card_of_injOn (fun C => A ∪ C)
    · intro C hC
      refine mem_filter.mpr ⟨mem_powerset.mpr (union_subset hA ?_), subset_union_left, ?_⟩
      · exact fun x hx => (hfree C hC hx).1
      · apply disjoint_left.mpr
        intro x hxB hx
        rcases mem_union.mp hx with hxA | hxC
        · exact disjoint_left.mp hAB hxA hxB
        · exact (hfree C hC hxC).2.2 hxB
    · intro C hC D hD he
      have hs := congrArg (fun E : Finset α => E \ A) he
      simpa only [union_sdiff_cancel_left (hdis C hC), union_sdiff_cancel_left (hdis D hD)] using hs
  have hfreecard : U.card - k ≤ free.card := by
    dsimp only [free]
    rw [card_sdiff_of_subset (union_subset hA hB), card_union_of_disjoint hAB]
    exact Nat.sub_le_sub_left hsize _
  have hlo : 2 ^ (U.card - k) ≤ good.card := by
    rw [card_powerset] at hgood
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hfreecard).trans hgood
  have he := card_filter_add_card_filter_not (s := U.powerset)
    (fun C => A ⊆ C ∧ Disjoint B C)
  rw [card_powerset] at he
  change good.card + _ = _ at he
  omega

/-- A common collection of subsets separates all pairs of disjoint supports,
as soon as the union bound for the failed separations is strictly below one. -/
theorem solution {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (U : Finset α) (I : Finset ι) (A B : ι → Finset α) (k t : ℕ)
    (hk : k ≤ U.card)
    (hpair : ∀ i ∈ I, A i ⊆ U ∧ B i ⊆ U ∧ Disjoint (A i) (B i) ∧
      (A i).card + (B i).card ≤ k)
    (hcount : I.card * (2 ^ k - 1) ^ t < (2 ^ k) ^ t) :
    ∃ f : Fin t → Finset α, (∀ j, f j ⊆ U) ∧
      ∀ i ∈ I, ∃ j, A i ⊆ f j ∧ Disjoint (B i) (f j) := by
  classical
  let Good (i : ι) (C : Finset α) : Prop := A i ⊆ C ∧ Disjoint (B i) C
  let All := Fintype.piFinset (fun _ : Fin t => U.powerset)
  let Bad (i : ι) := Fintype.piFinset (fun _ : Fin t => U.powerset.filter (fun C => ¬ Good i C))
  let F := 2 ^ U.card - 2 ^ (U.card - k)
  have hall : All.card = (2 ^ U.card) ^ t := by
    rw [Fintype.card_piFinset_const, card_powerset]
  have hbad (i : ι) (hi : i ∈ I) : (Bad i).card ≤ F ^ t := by
    obtain ⟨hA, hB, hAB, hsize⟩ := hpair i hi
    rw [Fintype.card_piFinset_const]
    exact Nat.pow_le_pow_left (failed_subsets U (A i) (B i) k hA hB hAB hsize) t
  have hspace : (2 : ℕ) ^ U.card = 2 ^ (U.card - k) * 2 ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hk]
  have hF : F = 2 ^ (U.card - k) * (2 ^ k - 1) := by
    dsimp only [F]
    rw [hspace, Nat.mul_sub_left_distrib, mul_one]
  have hstrict : I.card * F ^ t < (2 ^ U.card) ^ t := by
    calc
      _ = (2 ^ (U.card - k)) ^ t * (I.card * (2 ^ k - 1) ^ t) := by
        rw [hF, mul_pow]
        ac_rfl
      _ < (2 ^ (U.card - k)) ^ t * (2 ^ k) ^ t := by
        exact Nat.mul_lt_mul_of_pos_left hcount (by positivity)
      _ = _ := by rw [hspace, mul_pow]
  by_contra hex
  have hcover : All ⊆ I.biUnion Bad := by
    intro f hf
    have hfU : ∀ j, f j ⊆ U :=
      fun j => mem_powerset.mp (Fintype.mem_piFinset.mp hf j)
    have hn : ¬ (∀ i ∈ I, ∃ j, Good i (f j)) :=
      fun h => hex ⟨f, hfU, h⟩
    push Not at hn
    obtain ⟨i, hi, hfail⟩ := hn
    refine mem_biUnion.mpr ⟨i, hi, Fintype.mem_piFinset.mpr fun j => ?_⟩
    exact mem_filter.mpr ⟨mem_powerset.mpr (hfU j), hfail j⟩
  have hle : All.card ≤ I.card * F ^ t := calc
    _ ≤ (I.biUnion Bad).card := card_le_card hcover
    _ ≤ ∑ i ∈ I, (Bad i).card := card_biUnion_le
    _ ≤ ∑ _i ∈ I, F ^ t := sum_le_sum hbad
    _ = _ := by simp
  exact (not_lt_of_ge (hall ▸ hle)) hstrict

