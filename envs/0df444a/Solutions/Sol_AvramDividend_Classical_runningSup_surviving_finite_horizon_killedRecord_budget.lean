-- Prove2me | solution 1 for AvramDividend.Classical.runningSup_surviving_finite_horizon_killedRecord_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:49:44.218365+00:00
-- url     : https://prove2.me/submissions/f62b08ef-7c41-41b2-99ac-08027b513470

import Mathlib.Data.ENNReal.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_record_grid_last_survived_before_finite_horizon
import Theorems.Thm_AvramDividend_Classical_stopped_lintegral_zero_through_extended_first_record
import Theorems.Thm_AvramDividend_Classical_runningSup_finite_horizon_killedRecord_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal BigOperators

/-! Combine the final-record and no-record cases at every surviving finite horizon. -/
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
      if (⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞)) < τ then
        ENNReal.ofReal
          (h * Real.exp (-(q * ((⨅ (r : ℝ≥0) (_ : (0 : ℝ) + (k : ℝ) * h < X.X r ω), (r : ℝ≥0∞))).toReal)))
      else 0) := by
  classical
  rcases record_grid_last_survived_before_finite_horizon
      X ω 0 h hh t with hnone | ⟨N, hN, hnext⟩
  · have hz := stopped_lintegral_zero_through_extended_first_record
      X ω τ (fun r => ENNReal.ofReal (Real.exp (-(q * r)))) t
      (le_of_not_gt hnone)
    rw [hz]
    exact zero_le
  · exact runningSup_finite_horizon_killedRecord_budget
      X ω τ q h hq hh N t hN hnext htτ
