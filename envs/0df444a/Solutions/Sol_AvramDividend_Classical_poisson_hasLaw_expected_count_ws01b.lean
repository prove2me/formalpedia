-- Prove2me | solution 1 for AvramDividend.Classical.poisson_hasLaw_expected_count_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:04:46.971989+00:00
-- url     : https://prove2.me/submissions/d99c4cff-94d4-4fb2-a0b4-4c8d0d40917a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Nat

/-- A Poisson-distributed measurable count has mean equal to its rate,
independently of the private point-family definition. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) μ) :
    (∫ ω, (K ω : ℝ) ∂μ) = (r : ℝ) := by
  have hcast : AEStronglyMeasurable
      (fun n : ℕ => (n : ℝ)) (Measure.map K μ) :=
    (measurable_of_countable _).aestronglyMeasurable
  calc
    (∫ ω, (K ω : ℝ) ∂μ)
        = ∫ n, (n : ℝ) ∂(Measure.map K μ) := by
          exact (integral_map hK.aemeasurable hcast).symm
    _ = ∫ n, (n : ℝ) ∂(poissonMeasure r) := by
          rw [hLaw.map_eq]
    _ = (r : ℝ) :=
          poisson_count_expected_rate_ws01b r
