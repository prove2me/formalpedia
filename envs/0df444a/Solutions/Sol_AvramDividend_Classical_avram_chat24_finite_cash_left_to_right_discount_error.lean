-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_finite_cash_left_to_right_discount_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:35:14.389966+00:00
-- url     : https://prove2.me/submissions/88a5bac4-a4f0-468d-a59f-f1a0b7413ffa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Bounded coefficient errors propagate through finite nonnegative cash. -/
theorem solution
    {ι : Type*} (s : Finset ι) (eLeft eRight d : ι → ℝ) (ε : ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (he : ∀ i ∈ s, eLeft i - eRight i ≤ ε) :
    (∑ i ∈ s, eLeft i * d i) ≤
      (∑ i ∈ s, eRight i * d i) + ε * (∑ i ∈ s, d i) := by
  calc
    (∑ i ∈ s, eLeft i * d i) ≤
        ∑ i ∈ s, (eRight i * d i + ε * d i) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := mul_le_mul_of_nonneg_right (he i hi) (hd i hi)
      nlinarith
    _ = (∑ i ∈ s, eRight i * d i) + ε * (∑ i ∈ s, d i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
