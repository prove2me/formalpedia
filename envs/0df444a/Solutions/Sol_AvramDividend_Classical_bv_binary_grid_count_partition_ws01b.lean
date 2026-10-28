-- Prove2me | solution 1 for AvramDividend.Classical.bv_binary_grid_count_partition_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T00:20:53.899173+00:00
-- url     : https://prove2.me/submissions/a5969f68-348c-4ab2-88a0-e74ffd6625e0

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped BigOperators Classical

/-- Exact finite binary-grid partition: every sample with exactly k active
cells and no third cell outcome has a unique k-element active pattern. -/
theorem solution
    {Ω : Type*} (A B : ℕ → Set Ω) (n k : ℕ)
    (hExcl : ∀ i : ℕ, i < n → ∀ ω : Ω,
      ω ∈ A i → ω ∈ B i → False) :
    {ω : Ω | (∀ i : ℕ, i < n → ω ∈ A i ∨ ω ∈ B i) ∧
      ((Finset.range n).filter (fun i => ω ∈ A i)).card = k} =
    {ω : Ω | ∃ S ∈ Finset.powersetCard k (Finset.range n),
      ∀ i : ℕ, i < n →
        if i ∈ S then ω ∈ A i else ω ∈ B i} := by
  classical
  ext ω
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hCover, hCount⟩
    let S := (Finset.range n).filter (fun i => ω ∈ A i)
    have hSub : S ⊆ Finset.range n := Finset.filter_subset _ _
    refine ⟨S, Finset.mem_powersetCard.mpr ⟨hSub, hCount⟩, ?_⟩
    intro i hi
    by_cases hA : ω ∈ A i
    · have hiS : i ∈ S := by simp [S, hi, hA]
      simpa [hiS] using hA
    · have hiS : i ∉ S := by simp [S, hA]
      have hB : ω ∈ B i := (hCover i hi).resolve_left hA
      simpa [hiS] using hB
  · rintro ⟨S, hS, hPattern⟩
    obtain ⟨hSub, hCard⟩ := Finset.mem_powersetCard.mp hS
    have hFilter :
        (Finset.range n).filter (fun i => ω ∈ A i) = S := by
      ext i
      constructor
      · intro hMem
        obtain ⟨hRange, hA⟩ := Finset.mem_filter.mp hMem
        by_contra hiS
        have hB : ω ∈ B i := by
          simpa [hiS] using hPattern i (Finset.mem_range.mp hRange)
        exact hExcl i (Finset.mem_range.mp hRange) ω hA hB
      · intro hiS
        have hi : i < n := Finset.mem_range.mp (hSub hiS)
        have hA : ω ∈ A i := by simpa [hiS] using hPattern i hi
        exact Finset.mem_filter.mpr ⟨hSub hiS, hA⟩
    constructor
    · intro i hi
      by_cases hiS : i ∈ S
      · exact Or.inl (by simpa [hiS] using hPattern i hi)
      · exact Or.inr (by simpa [hiS] using hPattern i hi)
    · rw [hFilter, hCard]
