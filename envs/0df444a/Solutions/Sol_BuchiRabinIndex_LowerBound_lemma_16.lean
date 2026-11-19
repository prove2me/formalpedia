-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.lemma_16
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:17:03.865452+00:00
-- url     : https://prove2.me/submissions/0db47845-7c46-401d-b82d-0288b095121d

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Lemma16Aux
open BuchiRabinIndex.LowerBound
open scoped Classical

lemma mem_boundedWords (b : ℕ) : ∀ (d : ℕ) (x : Node),
    x ∈ boundedWords b d ↔ (∀ i ∈ x, 1 ≤ i ∧ i ≤ b) ∧ x.length ≤ d
  | 0, x => by cases x <;> simp [boundedWords]
  | d + 1, [] => by simp [boundedWords]
  | d + 1, i :: v => by
      have ih := mem_boundedWords b d v
      simp only [boundedWords, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc,
        Finset.mem_image, List.mem_cons, List.length_cons]
      constructor
      · rintro (h | ⟨j, hj, u, hu, he⟩)
        · cases h
        · obtain ⟨rfl, rfl⟩ := List.cons.inj he
          have := (mem_boundedWords b d u).1 hu
          refine ⟨?_, by omega⟩
          rintro k (rfl | hk)
          · exact hj
          · exact this.1 k hk
      · rintro ⟨h1, h2⟩
        right
        refine ⟨i, h1 i (Or.inl rfl), v, ih.2 ⟨fun k hk => h1 k (Or.inr hk), by omega⟩, rfl⟩

lemma le_sum_of_mem : ∀ (x : List ℕ) (i : ℕ), i ∈ x → i ≤ x.sum
  | [], _, h => by simp at h
  | a :: v, i, h => by
      rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := le_sum_of_mem v i h; simp; omega

lemma length_le_sum : ∀ (x : List ℕ), (∀ i ∈ x, 0 < i) → x.length ≤ x.sum
  | [], _ => by simp
  | a :: v, h => by
      have := length_le_sum v (fun i hi => h i (List.mem_cons_of_mem _ hi))
      have ha := h a (List.mem_cons_self ..)
      simp; omega

lemma mem_fullTree (n : ℕ) (hn : 1 ≤ n) (x : Node) :
    x ∈ fullTree n ↔ (∀ i ∈ x, 0 < i) ∧ x.sum ≤ n - 1 := by
  have hn0 : n ≠ 0 := by omega
  have hft : fullTree n = (boundedWords (n - 1) (n - 1)).filter (weight · ≤ n - 1) := by
    unfold fullTree; exact if_neg hn0
  rw [hft, Finset.mem_filter, mem_boundedWords]
  simp only [weight]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩
    exact ⟨fun i hi => (h1 i hi).1, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i hi => ⟨h1 i hi, ?_⟩, ?_⟩, h2⟩
    · have := le_sum_of_mem x i hi; omega
    · have := length_le_sum x h1; omega

end BuchiRabinIndex.LowerBound.Lemma16Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Lemma16Aux in
theorem solution (n : ℕ) (hn : 2 ≤ n) :
    fullTree n = {[]} ∪ part1 n ∪ part2 n ∧
    Set.BijOn phi1 {x | x ∈ part1 n} {x | x ∈ fullTree (n - 1)} ∧
    Set.BijOn phi2 {x | x ∈ part2 n} {x | x ∈ (fullTree (n - 1)).erase []} ∧
    (∀ x ∈ part1 n, weight x = weight (phi1 x) + 1) ∧
    (∀ x ∈ part2 n, weight x = weight (phi2 x) + 1) := by
  classical
  have M := mem_fullTree n (by omega)
  have M' := mem_fullTree (n - 1) (by omega)
  have hp1 : ∀ x, x ∈ part1 n ↔ ∃ v, v ∈ fullTree (n - 1) ∧ x = 1 :: v := by
    intro x; simp only [part1, Finset.mem_image]
    exact ⟨fun ⟨v, hv, e⟩ => ⟨v, hv, e.symm⟩, fun ⟨v, hv, e⟩ => ⟨v, hv, e.symm⟩⟩
  have hp2 : ∀ x, x ∈ part2 n ↔ ∃ i v, i :: v ∈ fullTree (n - 1) ∧ x = (i + 1) :: v := by
    intro x; simp only [part2, Finset.mem_image, Finset.mem_erase]
    constructor
    · rintro ⟨y, ⟨hy0, hy⟩, e⟩
      cases y with
      | nil => exact absurd rfl hy0
      | cons i v => exact ⟨i, v, hy, by simpa [increment] using e.symm⟩
    · rintro ⟨i, v, hy, rfl⟩
      exact ⟨i :: v, ⟨by simp, hy⟩, by simp [increment]⟩
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · ext x
    simp only [Finset.mem_union, Finset.mem_singleton, hp1, hp2, M, M']
    constructor
    · rintro ⟨h1, h2⟩
      cases x with
      | nil => exact Or.inl (Or.inl rfl)
      | cons a v =>
        have ha := h1 a (by simp)
        simp only [List.sum_cons] at h2
        by_cases ha1 : a = 1
        · subst ha1
          refine Or.inl (Or.inr ⟨v, ⟨fun i hi => h1 i (by simp [hi]), by omega⟩, rfl⟩)
        · refine Or.inr ⟨a - 1, v, ⟨?_, ?_⟩, by congr 1; omega⟩
          · intro i hi
            rcases List.mem_cons.1 hi with rfl | hi
            · omega
            · exact h1 i (by simp [hi])
          · simp only [List.sum_cons]; omega
    · rintro ((rfl | ⟨v, ⟨h1, h2⟩, rfl⟩) | ⟨i, v, ⟨h1, h2⟩, rfl⟩)
      · simp
      · refine ⟨?_, by simp only [List.sum_cons]; omega⟩
        intro i hi; rcases List.mem_cons.1 hi with rfl | hi
        · omega
        · exact h1 i hi
      · simp only [List.sum_cons] at h2
        refine ⟨?_, by simp only [List.sum_cons]; omega⟩
        intro j hj; rcases List.mem_cons.1 hj with rfl | hj
        · omega
        · exact h1 j (by simp [hj])
  · rintro x hx
    obtain ⟨v, hv, rfl⟩ := (hp1 x).1 hx
    simpa [phi1] using hv
  · rintro x hx y hy e
    obtain ⟨v, -, rfl⟩ := (hp1 x).1 hx
    obtain ⟨w, -, rfl⟩ := (hp1 y).1 hy
    simp [phi1] at e; rw [e]
  · rintro v hv
    exact ⟨1 :: v, (hp1 _).2 ⟨v, hv, rfl⟩, rfl⟩
  · rintro x hx
    obtain ⟨i, v, hv, rfl⟩ := (hp2 x).1 hx
    simp only [Set.mem_setOf_eq, Finset.mem_erase, phi2]
    exact ⟨by simp, by simpa using hv⟩
  · rintro x hx y hy e
    obtain ⟨i, v, -, rfl⟩ := (hp2 x).1 hx
    obtain ⟨j, w, -, rfl⟩ := (hp2 y).1 hy
    simp [phi2] at e; obtain ⟨rfl, rfl⟩ := e; rfl
  · rintro y hy
    simp only [Set.mem_setOf_eq, Finset.mem_erase] at hy
    obtain ⟨hy0, hy⟩ := hy
    cases y with
    | nil => exact absurd rfl hy0
    | cons i v =>
      refine ⟨(i + 1) :: v, (hp2 _).2 ⟨i, v, hy, rfl⟩, by simp [phi2]⟩
  · intro x hx
    obtain ⟨v, -, rfl⟩ := (hp1 x).1 hx
    simp [weight, phi1]; omega
  · intro x hx
    obtain ⟨i, v, -, rfl⟩ := (hp2 x).1 hx
    simp [weight, phi2]; omega
