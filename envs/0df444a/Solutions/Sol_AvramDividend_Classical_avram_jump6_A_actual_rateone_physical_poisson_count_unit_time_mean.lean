-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_A_actual_rateone_physical_poisson_count_unit_time_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T12:40:09.921282+00:00
-- url     : https://prove2.me/submissions/50cb391a-ad66-4161-a915-59ecb4042d0d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (N : Ω → ℕ)
    (hNm : Measurable N)
    (hLaw : P.map N = poissonMeasure (1 : ℝ≥0)) :
    (∫ ω, (N ω : ℝ) ∂P) = 1 := by
  have hCast : AEStronglyMeasurable (fun n : ℕ => (n : ℝ)) (P.map N) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).aestronglyMeasurable
  calc
    (∫ ω, (N ω : ℝ) ∂P) =
        ∫ n : ℕ, (n : ℝ) ∂(P.map N) := by
          rw [integral_map hNm.aemeasurable]
          exact hCast
    _ = ∫ n : ℕ, (n : ℝ) ∂(poissonMeasure (1 : ℝ≥0)) := by
          rw [hLaw]
    _ = 1 := by
          simpa using (poisson_count_expected_rate_ws01b (1 : ℝ≥0))
