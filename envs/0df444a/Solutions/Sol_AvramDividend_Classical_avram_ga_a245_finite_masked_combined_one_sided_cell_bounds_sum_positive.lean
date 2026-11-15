-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a245_finite_masked_combined_one_sided_cell_bounds_sum_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:21:13.710212+00:00
-- url     : https://prove2.me/submissions/70f0f958-8d22-4e24-a187-4fee40a0103b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (S : Finset ℕ) (A : ℕ → Prop) [DecidablePred A]
    (f g : ℕ → ℝ)
    (hg : ∀ i ∈ S, 0 ≤ g i)
    (hCell : ∀ i ∈ S, max (f i) 0 ≤ g i) :
    max (∑ i ∈ S, if A i then f i else 0) 0 ≤
      ∑ i ∈ S, if A i then g i else 0 := by
  have hSum : (∑ i ∈ S, if A i then f i else 0) ≤
      (∑ i ∈ S, if A i then g i else 0) := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : A i
    · simp only [if_pos h]
      exact (le_max_left _ _).trans (hCell i hi)
    · simp [h]
  have hNonneg : 0 ≤ (∑ i ∈ S, if A i then g i else 0) := by
    apply Finset.sum_nonneg
    intro i hi
    by_cases h : A i
    · simp only [if_pos h]
      exact hg i hi
    · simp [h]
  exact max_le hSum hNonneg
