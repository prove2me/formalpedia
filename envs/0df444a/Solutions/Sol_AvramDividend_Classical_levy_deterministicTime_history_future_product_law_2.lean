-- Prove2me | solution 2 for AvramDividend.Classical.levy_deterministicTime_history_future_product_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:06:00.335756+00:00
-- url     : https://prove2.me/submissions/cc093ec5-eb0e-4649-bac7-44774a087d10

import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_finite_time_state_future_product_of_cylinders
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Every adapted historical statistic factors from the stationary whole Lévy future. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω : Ω => (H ω, fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
  calc
    _ = (Measure.map H P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 =>
          X.X (s + t) ω - X.X s ω) P) :=
      finite_time_state_future_product_of_cylinders X s H hH
        (finite_future_increment_sigma_indep_past X s)
    _ = _ := by rw [levy_shiftedFuturePath_stationary_law X s]
