-- Prove2me | solution 1 for BanditAlgorithm.gittinsRetirementValue_eq_zero_iff_index_le
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-31T04:09:21.450165+00:00
-- url     : https://prove2.me/submissions/044b7ef4-6483-4dfb-859c-a31c12488f7c

import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_eq_zero_of_index_le
import Theorems.Thm_BanditAlgorithm_gittinsRetirementValue_pos_of_lt_index

open MeasureTheory ProbabilityTheory ENNReal
open BanditAlgorithm

theorem solution
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α)
    (x : S) (γ : ℝ) :
    gittinsRetirementValue P r α γ x = 0 ↔
      gittinsIndex P r α x ≤ γ := by
  constructor
  · intro hv
    by_contra hle
    have hpos := gittinsRetirementValue_pos_of_lt_index
      P hr hα0 hα1 hint x γ (lt_of_not_ge hle)
    rw [hv] at hpos
    exact lt_irrefl 0 hpos
  · exact gittinsRetirementValue_eq_zero_of_index_le
      P hr hα0 hα1 hint x γ
