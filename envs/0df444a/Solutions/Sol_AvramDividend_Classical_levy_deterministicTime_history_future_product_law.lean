-- Prove2me | solution 1 for AvramDividend.Classical.levy_deterministicTime_history_future_product_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:05:58.022251+00:00
-- url     : https://prove2.me/submissions/e606f291-fb34-4772-8d59-6a2a0865796f

import Mathlib.Probability.Independence.Basic
import Theorems.Thm_AvramDividend_Classical_finite_time_state_future_product_of_cylinders
import Theorems.Thm_AvramDividend_Classical_finite_future_increment_sigma_indep_past
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕) (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    Measure.map
      (fun ω : Ω => (H ω, fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P =
      (Measure.map H P).prod
        (Measure.map (fun ω : Ω => fun t : ℝ≥0 => X.X t ω) P) := by
  rw [AvramDividend.Classical.finite_time_state_future_product_of_cylinders X s H hH
    (AvramDividend.Classical.finite_future_increment_sigma_indep_past X s),
    AvramDividend.Classical.levy_shiftedFuturePath_stationary_law X s]
