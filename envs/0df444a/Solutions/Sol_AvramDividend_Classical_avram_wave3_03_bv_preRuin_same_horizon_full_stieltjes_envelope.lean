-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_preRuin_same_horizon_full_stieltjes_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:44:17.82702+00:00
-- url     : https://prove2.me/submissions/68ec67c5-6976-4888-a8fe-b84586896558

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_preRuin_eventually_right_solvent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- All genuine Stieltjes dividends through strict pre-ruin T are bounded by
initial capital plus the physical BV drift by precisely time T, including
the payment atom immediately after T and every continuous payment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : ℝ≥0∞) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, (T : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
  filter_upwards [
      avram_wave3_03_bv_same_horizon_stopped_payment_drift_envelope
        X hBV x D hD q hq σ T] with ω hω
  intro hT
  exact hω (avram_wave3_03_preRuin_eventually_right_solvent
    X x D ω T hT)