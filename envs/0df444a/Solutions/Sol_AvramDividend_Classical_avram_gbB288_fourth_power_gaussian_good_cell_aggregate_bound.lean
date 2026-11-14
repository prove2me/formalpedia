-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB288_fourth_power_gaussian_good_cell_aggregate_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:06:58.049805+00:00
-- url     : https://prove2.me/submissions/8c6c981b-7028-40bf-8d17-39fe5acfe501

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB281_fourth_power_gaussian_total_good_cell_time_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Finset AvramDividend.Classical
noncomputable section

/-- Integrated good-cell bounds sum to the correct inverse-refinement rate. -/
theorem solution (n m : ℕ) (hm : 0 < m) (f : ℕ → ℝ)
    (hf : ∀ i ∈ Finset.range (n * m ^ 4),
      f i ≤ (1 / ((m : ℝ) ^ 3)) *
        (∫ t in ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))..
          (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
          (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)))) :
    (∑ i ∈ Finset.range (n * m ^ 4), f i) ≤
      2 * (n : ℝ) / (m : ℝ) := by
  calc
    (∑ i ∈ Finset.range (n * m ^ 4), f i) ≤
        (∑ i ∈ Finset.range (n * m ^ 4),
          (1 / ((m : ℝ) ^ 3)) *
            (∫ t in ((i : ℝ) * (1 / ((m : ℝ) ^ 4)))..
              (((i : ℝ) + 1) * (1 / ((m : ℝ) ^ 4))),
              (t - (i : ℝ) * (1 / ((m : ℝ) ^ 4))) ^ (-(1 / 2 : ℝ)))) := by
          exact Finset.sum_le_sum (fun i hi => hf i hi)
    _ = _ := avram_gbB281_fourth_power_gaussian_total_good_cell_time_kernel n m hm
