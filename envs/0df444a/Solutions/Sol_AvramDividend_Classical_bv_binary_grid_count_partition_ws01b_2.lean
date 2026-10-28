-- Prove2me | solution 2 for AvramDividend.Classical.bv_binary_grid_count_partition_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T00:21:21.012988+00:00
-- url     : https://prove2.me/submissions/c612e7ea-2465-4cb9-8bba-468f13ffd701

import Mathlib

open Set
open scoped BigOperators Classical

theorem solution
    {Ω : Type*} (A B : ℕ → Set Ω) (n k : ℕ)
    (hExcl : ∀ i : ℕ, i < n → ∀ ω : Ω,
      ω ∈ A i → ω ∈ B i → False) :
    {ω : Ω | (∀ i : ℕ, i < n → ω ∈ A i ∨ ω ∈ B i) ∧
      ((Finset.range n).filter (fun i => ω ∈ A i)).card = k} =
    {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
      ∀ i : ℕ, i < n →
        if i ∈ S then ω ∈ A i else ω ∈ B i} := by
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hAB, hc⟩
    refine ⟨(Finset.range n).filter (fun i => ω ∈ A i), ?_, ?_⟩
    · rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, hc⟩
    · intro i hi
      by_cases hA : ω ∈ A i
      · rw [if_pos (by simp [hi, hA])]; exact hA
      · rw [if_neg (by simp [hA])]
        exact (hAB i hi).resolve_left hA
  · rintro ⟨S, hS, hSi⟩
    rw [Finset.mem_powersetCard] at hS
    obtain ⟨hsub, hcard⟩ := hS
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hSi i hi
      split_ifs at this
      · exact Or.inl this
      · exact Or.inr this
    · have : (Finset.range n).filter (fun i => ω ∈ A i) = S := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · rintro ⟨hi, hA⟩
          by_contra hn
          have := hSi i hi
          rw [if_neg hn] at this
          exact hExcl i hi ω hA this
        · intro hiS
          have hi : i < n := Finset.mem_range.mp (hsub hiS)
          have := hSi i hi
          rw [if_pos hiS] at this
          exact ⟨hi, this⟩
      rw [this, hcard]
