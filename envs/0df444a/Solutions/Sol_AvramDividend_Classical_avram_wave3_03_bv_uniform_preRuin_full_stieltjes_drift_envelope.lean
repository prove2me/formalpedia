-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:43:43.41884+00:00
-- url     : https://prove2.me/submissions/756546de-2fb5-4330-b4c5-c99b656c8e74

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightLimit_and_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_preRuin_eventually_right_solvent

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- One source-probability-one event controls all pre-ruin horizons and all
payment stopping sets simultaneously, including random horizons and clocks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (σ : ℝ≥0∞),
      (T : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
    with ω hmono
  intro T σ hpre
  have hnear := avram_wave3_03_preRuin_eventually_right_solvent
    X x D ω T hpre
  have hpost : 0 ≤ x + X.X T ω - rightLimit D T ω :=
    (postPaymentReserve_rightLimit_and_nonnegative X x D hD ω T).2 hnear
  have hmono0 :
      (0 : ℝ) * X.drift - X.X 0 ω ≤
        (T : ℝ) * X.drift - X.X T ω :=
    hmono (show (0 : ℝ≥0) ≤ T from zero_le)
  have hX : X.X T ω ≤ (T : ℝ) * X.drift := by
    have hh : 0 ≤ (T : ℝ) * X.drift - X.X T ω := by
      simpa [X.X_zero ω] using hmono0
    linarith
  calc
    _ ≤ ENNReal.ofReal (rightLimit D T ω) :=
      avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
        q hq D hD ω σ T
    _ ≤ ENNReal.ofReal (x + (T : ℝ) * X.drift) :=
      ENNReal.ofReal_le_ofReal (by linarith)
