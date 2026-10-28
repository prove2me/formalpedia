-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_survival_deficit_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T08:25:32.18287+00:00
-- url     : https://prove2.me/submissions/5482f8fd-1491-465a-89a0-328c811a637a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_actual_survival_deficit_integrable_of_origin_zero
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    Integrable
      ({ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω}.indicator
        (fun ω => (T : ℝ) * X.drift - X.X T ω)) P := by
  have hXT : Measurable (X.X T) := (X.adapted T).mono (𝓕.le T) le_rfl
  have hS : MeasurableSet {ω : Ω | (T : ℝ≥0∞) < barrierRuinTime X 0 ω} :=
    measurableSet_lt measurable_const (barrierRuinTime_measurable X 0)
  have hf : Measurable (fun ω => (T : ℝ) * X.drift - X.X T ω) := measurable_const.sub hXT
  exact bv_actual_survival_deficit_integrable_of_origin_zero X hStanding hBV T X.X_zero
    ((hf.indicator hS).aestronglyMeasurable)
