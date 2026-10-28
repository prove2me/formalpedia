-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_deficit_implies_linear_running_sup_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:01:35.20345+00:00
-- url     : https://prove2.me/submissions/af324bed-be2c-414f-8ca6-b9f00147db67

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_drift_deficit_zero_time_forces_linear_prefix
import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual bounded-variation paths earn a linear running record before the first deficit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      X.drift * (t : ℝ) - X.X t ω = 0 →
        runningSup X t ω = X.drift * (t : ℝ) := by
  have hDrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hStanding hBV).1
  refine (bv_drift_deficit_ae_monotone_all_times X hBV).mono ?_
  intro ω hMono t hZero
  have hLinear := drift_deficit_zero_time_forces_linear_prefix
    X ω (X.X_zero ω) hMono t hZero
  exact runningSup_linear_of_linear_capital_prefix
    X ω t hDrift hLinear
