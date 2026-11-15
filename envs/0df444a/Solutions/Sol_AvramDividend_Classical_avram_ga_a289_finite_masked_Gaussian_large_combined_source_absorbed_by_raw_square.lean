-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a289_finite_masked_Gaussian_large_combined_source_absorbed_by_raw_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T10:18:45.435769+00:00
-- url     : https://prove2.me/submissions/1d9b4ff4-d1bf-40f5-98a9-218654410de3

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} (S : Finset ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (e0 e1 w0 w1 d h r z T : ℕ → Ω → ℝ)
    (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hCell : ∀ i ω, A i ω →
      0 ≤ e0 i ω ∧ e0 i ω ≤ 1 ∧
      0 ≤ e1 i ω ∧ e1 i ω ≤ 1 ∧
      0 ≤ T i ω ∧ |w0 i ω| ≤ B ∧
      |d i ω| ≤ B ∧ |h i ω| ≤ B ∧
      w1 i ω ≤ T i ω)
    (hLarge : ∀ i ω, A i ω → δ ≤ |r i ω|)
    (hDrift : ∀ i ω, A i ω → |r i ω-z i ω| ≤ δ)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then
      e1 i ω*(w1 i ω-w0 i ω) -
        e0 i ω*(d i ω*r i ω+h i ω/2*(z i ω)^2)
      else 0) 0 ≤
    ∑ i ∈ S, if A i ω then
      T i ω+B*(1/δ^2+1/δ+2)*(r i ω)^2
      else 0 := by
  have hBase := avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
    S A e0 e1 w0 w1 d h r z T B hB hCell ω
  apply le_trans hBase
  apply Finset.sum_le_sum
  intro i hi
  by_cases ha : A i ω
  · simp only [if_pos ha]
    have hRate := avram_ga_a261_large_increment_small_drift_raw_square_dominates_source_polynomial
      δ (r i ω) (z i ω) (r i ω-z i ω) hδ
      (hLarge i ω ha) (hDrift i ω ha) (by ring)
    have hScaled := mul_le_mul_of_nonneg_left hRate hB
    linarith
  · simp only [if_neg ha, le_refl]
