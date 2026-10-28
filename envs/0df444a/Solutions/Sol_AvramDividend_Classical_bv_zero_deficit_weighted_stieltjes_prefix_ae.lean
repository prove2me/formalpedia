-- Prove2me | solution 1 for AvramDividend.Classical.bv_zero_deficit_weighted_stieltjes_prefix_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T12:26:44.43763+00:00
-- url     : https://prove2.me/submissions/6c25dd2c-ecba-4b40-8962-a7a1d1b694ee

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_drift_deficit_zero_time_forces_linear_prefix
import Theorems.Thm_AvramDividend_Classical_runningSup_linear_of_linear_capital_prefix
import Theorems.Thm_AvramDividend_Classical_runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual bounded-variation process pays linear Stieltjes dividends
    throughout every prefix on which its drift deficit remains zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      X.drift * (T : ℝ) - X.X T ω = 0 →
      ∀ f : ℝ → ℝ≥0∞,
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂(dividendMeasure (runningSup X) ω)) =
        (∫⁻ t in Ioc (0 : ℝ) (T : ℝ), f t
          ∂((ENNReal.ofReal X.drift) • volume)) := by
  have hDrift : 0 ≤ X.drift :=
    le_of_lt (bv_standing_drift_pos X hStanding hBV).1
  refine (bv_drift_deficit_ae_monotone_all_times X hBV).mono ?_
  intro ω hMono T hZero f
  have hLinear : ∀ u : ℝ≥0, u ≤ T →
      X.X u ω = X.drift * (u : ℝ) :=
    drift_deficit_zero_time_forces_linear_prefix
      X ω (X.X_zero ω) hMono T hZero
  have hPath : ∀ u : ℝ, 0 ≤ u → u ≤ (T : ℝ) →
      runningSup X u.toNNReal ω = X.drift * u := by
    intro u hu huT
    have huNN : u.toNNReal ≤ T := by
      have hReal : (u.toNNReal : ℝ) ≤ (T : ℝ) := by
        simpa only [Real.coe_toNNReal u hu] using huT
      exact_mod_cast hReal
    have hRunning :=
      runningSup_linear_of_linear_capital_prefix
        X ω u.toNNReal hDrift
        (fun s hs => hLinear s (le_trans hs huNN))
    simpa only [Real.coe_toNNReal u hu] using hRunning
  exact runningSup_drift_prefix_discounted_stieltjes_eq_scaled_volume
    X ω (T : ℝ) (NNReal.coe_nonneg T) hPath hDrift f
