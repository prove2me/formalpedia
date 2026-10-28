-- Prove2me | solution 1 for AvramDividend.Classical.poisson_past_weighted_count_compensation_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:15:40.555284+00:00
-- url     : https://prove2.me/submissions/915d24e5-c20f-4406-a71b-4c4cbf1663f6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_hasLaw_expected_count_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- One-step predictable Poisson count compensation: an integrable
past observable times an independent future Poisson count has expected
product equal to the past mean times the future jump intensity. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : Ω → ℝ) (hHm : Measurable H) (hHi : Integrable H μ)
    (K : Ω → ℕ) (hKm : Measurable K)
    (hIndep : IndepFun H K μ)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) μ) :
    (∫ ω, H ω * (K ω : ℝ) ∂μ) =
      (∫ ω, H ω ∂μ) * (r : ℝ) := by
  have hfactor :
      (∫ ω, H ω * (K ω : ℝ) ∂μ) =
      (∫ ω, H ω ∂μ) *
        (∫ ω, (K ω : ℝ) ∂μ) := by
    exact hIndep.integral_fun_comp_mul_comp
      (f := fun a : ℝ => a)
      (g := fun n : ℕ => (n : ℝ))
      hHm.aemeasurable hKm.aemeasurable
      measurable_id.aestronglyMeasurable
      (measurable_of_countable _).aestronglyMeasurable
  rw [hfactor, poisson_hasLaw_expected_count_ws01b μ K hKm r hLaw]
