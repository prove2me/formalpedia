-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a246_masked_combined_one_sided_small_large_cell_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:28:19.921243+00:00
-- url     : https://prove2.me/submissions/65716741-0cfe-4213-9914-676054b0bb22

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
noncomputable section

theorem solution
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (f R u v : ℕ → ℝ) (δ : ℝ)
    (hu : ∀ i ∈ S, 0 ≤ u i)
    (hv : ∀ i ∈ S, 0 ≤ v i)
    (hSmall : ∀ i ∈ S, |R i| < δ → max (f i) 0 ≤ u i)
    (hLarge : ∀ i ∈ S, δ ≤ |R i| → max (f i) 0 ≤ v i) :
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      (∑ i ∈ S, if A i then
        if |R i| < δ then u i else v i else 0) := by
  apply max_le_iff.mpr
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    by_cases hA : A i
    · simp only [if_pos hA]
      by_cases hR : |R i| < δ
      · simp only [if_pos hR]
        exact (le_max_left (f i) 0).trans (hSmall i hi hR)
      · simp only [if_neg hR]
        exact (le_max_left (f i) 0).trans
          (hLarge i hi (le_of_not_gt hR))
    · simp only [if_neg hA, le_refl]
  · apply Finset.sum_nonneg
    intro i hi
    by_cases hA : A i
    · simp only [if_pos hA]
      by_cases hR : |R i| < δ
      · simpa [hR] using hu i hi
      · simpa [hR] using hv i hi
    · simp only [if_neg hA, le_refl]
