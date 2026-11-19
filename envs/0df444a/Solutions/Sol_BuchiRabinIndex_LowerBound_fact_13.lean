-- Prove2me | solution 1 for BuchiRabinIndex.LowerBound.fact_13
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:11:22.153591+00:00
-- url     : https://prove2.me/submissions/fc409387-c99b-44a9-9fc2-3343a5e5c39f

import Definitions.Def_BuchiRabinIndex_LowerBound_Nodes

set_option autoImplicit false

namespace BuchiRabinIndex.LowerBound.Fact13Aux
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

lemma mem_filter_iff (n w : ℕ) (hn : 1 ≤ n) (hw : w ≤ n - 1) (x : Node) :
    x ∈ (fullTree n).filter (weight · = w) ↔ (∀ i ∈ x, 0 < i) ∧ x.sum = w := by
  have hn0 : n ≠ 0 := by omega
  have hft : fullTree n = (boundedWords (n - 1) (n - 1)).filter (weight · ≤ n - 1) := by
    unfold fullTree; exact if_neg hn0
  rw [Finset.mem_filter, hft, Finset.mem_filter, mem_boundedWords]
  simp only [weight]
  constructor
  · rintro ⟨⟨⟨h1, _⟩, _⟩, h3⟩
    exact ⟨fun i hi => (h1 i hi).1, h3⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨⟨fun i hi => ⟨h1 i hi, ?_⟩, ?_⟩, by omega⟩, h2⟩
    · have := le_sum_of_mem x i hi; omega
    · have := length_le_sum x h1; omega

lemma filter_eq (n w : ℕ) (hn : 1 ≤ n) (hw : w ≤ n - 1) :
    (fullTree n).filter (weight · = w) =
      (Finset.univ : Finset (Composition w)).image Composition.blocks := by
  ext x
  rw [mem_filter_iff n w hn hw, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨x, fun hi => h1 _ hi, h2⟩, Finset.mem_univ _, rfl⟩
  · rintro ⟨c, -, rfl⟩
    exact ⟨fun i hi => c.blocks_pos hi, c.blocks_sum⟩

lemma card_filter (n w : ℕ) (hn : 1 ≤ n) (hw : w ≤ n - 1) :
    ((fullTree n).filter (weight · = w)).card = 2 ^ (w - 1) := by
  rw [filter_eq n w hn hw, Finset.card_image_of_injective _ (fun a b h => Composition.ext h),
    Finset.card_univ, composition_card]

lemma sum_pow : ∀ n : ℕ, 1 ≤ n → ∑ w ∈ Finset.range n, 2 ^ (w - 1) = 2 ^ (n - 1)
  | 0, h => by omega
  | 1, _ => by simp
  | n + 2, _ => by
      rw [Finset.sum_range_succ, sum_pow (n + 1) (by omega)]
      rw [show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega, pow_succ]; ring

end BuchiRabinIndex.LowerBound.Fact13Aux

open BuchiRabinIndex.LowerBound BuchiRabinIndex.LowerBound.Fact13Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) :
    (fullTree n).card = 2 ^ (n - 1) ∧
    (fullTree n).filter (weight · = 0) = {[]} ∧
    ∀ w, 0 < w → w ≤ n - 1 →
      ((fullTree n).filter (weight · = w)).card = 2 ^ (w - 1) := by
  classical
  refine ⟨?_, ?_, fun w _ hw => card_filter n w hn hw⟩
  · have hmap : ∀ x ∈ fullTree n, weight x ∈ Finset.range n := by
      intro x hx
      have hn0 : n ≠ 0 := by omega
      rw [fullTree, if_neg hn0, Finset.mem_filter] at hx
      simp only [Finset.mem_range]; omega
    rw [Finset.card_eq_sum_card_fiberwise hmap, ← sum_pow n hn]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    rw [Finset.mem_range] at hw
    exact card_filter n w hn (by omega)
  · rw [Finset.eq_singleton_iff_unique_mem, mem_filter_iff n 0 hn (by omega)]
    refine ⟨⟨by simp, rfl⟩, ?_⟩
    intro x hx
    obtain ⟨h1, h2⟩ := (mem_filter_iff n 0 hn (by omega) x).1 hx
    cases x with
    | nil => rfl
    | cons a v =>
      have := h1 a (List.mem_cons_self ..); simp at h2; omega
