-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_stopped_partition_reward_eq_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:18:49.619968+00:00
-- url     : https://prove2.me/submissions/f9d7b263-9de7-4bc4-88b8-f17ea29fb4e8

import Theorems.Thm_AvramDividend_Classical_recordPartition_pointwise_tsum_indicator
import Theorems.Thm_AvramDividend_Classical_runningSup_stopped_lintegral_countable_interchange
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n) :
    (∫⁻ r in paymentTimes τ, if u 0 < r then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
  calc
    (∫⁻ r in paymentTimes τ, if u 0 < r then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) =
      (∫⁻ r in paymentTimes τ,
        (∑' i : ℕ,
          if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0)
          ∂(dividendMeasure (runningSup X) ω)) := by
        apply lintegral_congr
        intro r
        exact (recordPartition_pointwise_tsum_indicator
          u hu hcofinal r (w r)).symm
    _ = (∑' i : ℕ,
      ∫⁻ r in paymentTimes τ,
        if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) :=
      runningSup_stopped_lintegral_countable_interchange X ω τ w hw u
