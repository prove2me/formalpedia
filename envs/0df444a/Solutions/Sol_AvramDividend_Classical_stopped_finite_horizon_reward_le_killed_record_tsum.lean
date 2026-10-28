-- Prove2me | solution 1 for AvramDividend.Classical.stopped_finite_horizon_reward_le_killed_record_tsum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:58:12.796475+00:00
-- url     : https://prove2.me/submissions/3a01ef58-a09c-4209-944c-a37179fa6768

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_record_grid_last_survived_before_finite_horizon
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_zero_through_extended_first_record
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_killedRecord_budget
import Theorems.Thm_AvramDividend_Classical_chat08_named_upper_clock_eq_raw_infimum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q h : ℝ) (hq : 0 ≤ q) (hh : 0 < h)
    (t : ℝ≥0) (htτ : (t : ℝ≥0∞) < τ) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (t : ℝ)
      then ENNReal.ofReal (Real.exp (-(q * r))) else 0
      ∂(dividendMeasure (runningSup X) ω)) ≤
    (∑' k : ℕ,
      if twoSidedExitUpTime X ((k : ℝ) * h) ω < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q *
            (twoSidedExitUpTime X ((k : ℝ) * h) ω).toReal)))
      else 0) := by
  rcases record_grid_last_survived_before_finite_horizon X ω 0 h hh t with hzero | ⟨N, hN, hnext⟩
  · have ht : (t : ℝ≥0∞) ≤
        (⨅ (r : ℝ≥0) (_ : (0 : ℝ) < X.X r ω), (r : ℝ≥0∞)) :=
      le_of_not_gt hzero
    rw [stopped_lintegral_zero_through_extended_first_record
      X ω τ (fun r => ENNReal.ofReal (Real.exp (-(q * r)))) t ht]
    exact zero_le
  · simpa only [zero_add, chat08_named_upper_clock_eq_raw_infimum] using
      (runningSup_finite_horizon_killedRecord_budget
        X ω τ q h hq hh N t hN hnext htτ)
