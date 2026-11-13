-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_bounded_simple_mark_sum_norm_dominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:01:02.68122+00:00
-- url     : https://prove2.me/submissions/561d0c74-fcbc-4bd2-92b8-08d5f958bf5f

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section
theorem solution
    {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (a N r : ι → ℝ)
    (ha : ∀ i ∈ F, |a i| ≤ 1)
    (hN : ∀ i ∈ F, 0 ≤ N i)
    (hr : ∀ i ∈ F, 0 ≤ r i) :
    |∑ i ∈ F, a i * (N i - r i)| ≤
      ∑ i ∈ F, (N i + r i) := by
  calc
    |∑ i ∈ F, a i * (N i - r i)| ≤
        ∑ i ∈ F, |a i * (N i - r i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ F, (N i + r i) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have h1 : |a i| * |N i - r i| ≤ |N i - r i| := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (ha i hi)
            (abs_nonneg (N i - r i))
      have h2 : |N i - r i| ≤ N i + r i := by
        calc
          |N i - r i| ≤ |N i - (0 : ℝ)| + |(0 : ℝ) - r i| :=
            abs_sub_le (N i) 0 (r i)
          _ = N i + r i := by
            simp [abs_of_nonneg (hN i hi), abs_of_nonneg (hr i hi)]
      exact h1.trans h2
