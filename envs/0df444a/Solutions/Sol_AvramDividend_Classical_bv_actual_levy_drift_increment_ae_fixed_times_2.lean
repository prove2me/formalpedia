-- Prove2me | solution 2 for AvramDividend.Classical.bv_actual_levy_drift_increment_ae_fixed_times
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:12:30.709985+00:00
-- url     : https://prove2.me/submissions/840c2a6a-df51-48a1-b996-27bab0f678bb

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.OuterMeasure.AE

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

/-- Transfer the canonical bounded-variation drift bound to a stationary Lévy increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      X.X t ω - X.X s ω ≤ ((t - s : ℝ≥0) : ℝ) * X.drift := by
  have hIdent :
      IdentDistrib
        (fun ω => X.X t ω - X.X s ω)
        (X.X (t - s)) P P := X.stationaryIncrements s t hst
  have hFixed :
      ∀ᵐ ω ∂P,
        X.X (t - s) ω ≤ ((t - s : ℝ≥0) : ℝ) * X.drift :=
    bv_actual_levy_drift_upper_ae_fixed_time X hBV (t - s)
  exact hIdent.symm.ae_snd measurableSet_Iic hFixed
