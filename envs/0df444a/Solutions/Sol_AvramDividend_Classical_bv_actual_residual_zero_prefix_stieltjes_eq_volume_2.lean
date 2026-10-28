-- Prove2me | solution 2 for AvramDividend.Classical.bv_actual_residual_zero_prefix_stieltjes_eq_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:11:43.16542+00:00
-- url     : https://prove2.me/submissions/2572f6a5-3183-4454-8c35-46e7a0f06249

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_runningSup_linear
import Theorems.Thm_AvramDividend_Classical_runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A zero-residual history identifies the stopped record measure with drift volume. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (ω : Ω) (T : ℝ) (hT : 0 ≤ T)
    (hHistory : ∀ s : ℝ≥0, s ≤ Real.toNNReal T →
      (s : ℝ) * X.drift - X.X s ω = 0)
    (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂(dividendMeasure (runningSup X) ω)) =
    (∫⁻ t in Ioc (0 : ℝ) T, f t ∂((ENNReal.ofReal X.drift) • volume)) := by
  have hDrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hStanding hBV).1
  apply runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
    X ω T hT ?_ hDrift f
  intro u hu huT
  have hlinear :=
    bv_actual_residual_zero_prefix_runningSup_linear
      X hStanding hBV ω (Real.toNNReal T) hHistory
      (Real.toNNReal u) (Real.toNNReal_mono huT)
  simpa only [Real.coe_toNNReal u hu] using hlinear
