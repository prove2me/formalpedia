-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_residual_zero_prefix_stieltjes_eq_volume
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:10:50.761989+00:00
-- url     : https://prove2.me/submissions/decccf3b-245a-4ec1-8f9f-5af5d83a6d67

import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_prefix_runningSup_linear
import Theorems.Thm_AvramDividend_Classical_runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The genuine Stieltjes dividend measure on a zero-residual path prefix equals drift times volume. -/
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
  have hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u := by
    intro u hu huT
    have hut : u.toNNReal ≤ T.toNNReal :=
      (Real.toNNReal_le_iff_le_coe).2 (by
        simpa only [Real.coe_toNNReal T hT] using huT)
    have hRec := bv_actual_residual_zero_prefix_runningSup_linear
      X hStanding hBV ω T.toNNReal hHistory u.toNNReal hut
    simpa only [Real.coe_toNNReal u hu] using hRec
  exact runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
    X ω T hT hPath (bv_standing_drift_pos X hStanding hBV).1.le f
