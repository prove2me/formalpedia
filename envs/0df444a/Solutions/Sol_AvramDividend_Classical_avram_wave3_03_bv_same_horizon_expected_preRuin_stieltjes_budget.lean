-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_same_horizon_expected_preRuin_stieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:49:57.41735+00:00
-- url     : https://prove2.me/submissions/c23ef0e8-597a-4eb8-8e02-0c5e0729f227

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

/-- Same-horizon expected discounted full Stieltjes dividends survive
localisation with the exact physical BV drift budget. The random cutoff may
be the original ruin clock; all diffuse dividend mass is retained. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞) (T : ℝ≥0) :
    (∫⁻ ω, if (T : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
  have hmajor : ∀ᵐ ω ∂P,
      (if (T : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
        else 0) ≤ ENNReal.ofReal (x + (T : ℝ) * X.drift) := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hmono
    split_ifs with hpre
    · have hnear := avram_wave3_03_preRuin_eventually_right_solvent
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
            q hq D hD ω (σ ω) T
        _ ≤ ENNReal.ofReal (x + (T : ℝ) * X.drift) :=
          ENNReal.ofReal_le_ofReal (by linarith)
    · simp
  letI : IsProbabilityMeasure P := X.isProbability
  calc
    _ ≤ (∫⁻ ω, ENNReal.ofReal (x + (T : ℝ) * X.drift) ∂P) :=
      lintegral_mono_ae hmajor
    _ = ENNReal.ofReal (x + (T : ℝ) * X.drift) := by simp
