-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_survival_deficit_integrable_of_origin_zero
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T07:57:29.830535+00:00
-- url     : https://prove2.me/submissions/c66fc30c-8f0b-401e-9343-5a0603f5eca6

import Theorems.Thm_AvramDividend_Classical_bounded_survival_deficit_indicator_integrable
import Theorems.Thm_AvramDividend_Classical_zero_reflected_ruin_strict_survival_capital_monotone_prefix
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hOrigin : ∀ ω : Ω, X.X 0 ω = 0)
    (hMeas : AEStronglyMeasurable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P) :
    Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P := by
  haveI := X.isProbability
  have hd := (bv_standing_drift_pos X hStanding hBV).1
  refine bounded_survival_deficit_indicator_integrable P _ _ ((T : ℝ) * X.drift) (by positivity) hMeas ?_ ?_
  · filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV T] with ω hω
    linarith
  · intro ω hω
    have h := zero_reflected_ruin_strict_survival_capital_monotone_prefix X ω T hω 0 T (by simp) le_rfl
    rw [hOrigin ω] at h
    linarith
