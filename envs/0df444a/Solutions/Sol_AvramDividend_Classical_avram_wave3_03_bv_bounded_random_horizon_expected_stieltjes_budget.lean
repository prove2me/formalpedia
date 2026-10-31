-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_bounded_random_horizon_expected_stieltjes_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T10:50:20.915053+00:00
-- url     : https://prove2.me/submissions/0001e95c-6f95-4fc5-a3d4-6f4acf8dcc92

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

/-- The whole stopped Stieltjes payout before ruin has a uniform expectation
bound along any bounded path-dependent approximating horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T : Ω → ℝ≥0) (H : ℝ≥0) (hTH : ∀ ω, T ω ≤ H) :
    (∫⁻ ω, if ((T ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic ((T ω : ℝ≥0) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (x + (H : ℝ) * max 0 X.drift) := by
  have hmajor : ∀ᵐ ω ∂P,
      (if ((T ω : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω then
        (∫⁻ r in paymentTimes (σ ω) ∩ Iic ((T ω : ℝ≥0) : ℝ),
          ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
        else 0) ≤ ENNReal.ofReal (x + (H : ℝ) * max 0 X.drift) := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hmono
    split_ifs with hpre
    · have hnear := avram_wave3_03_preRuin_eventually_right_solvent
        X x D ω (T ω) hpre
      have hpost : 0 ≤ x + X.X (T ω) ω - rightLimit D (T ω) ω :=
        (postPaymentReserve_rightLimit_and_nonnegative X x D hD ω (T ω)).2 hnear
      have hmono0 :
          (0 : ℝ) * X.drift - X.X 0 ω ≤
            (T ω : ℝ) * X.drift - X.X (T ω) ω :=
        hmono (show (0 : ℝ≥0) ≤ T ω from zero_le)
      have hX : X.X (T ω) ω ≤ (T ω : ℝ) * X.drift := by
        have hh : 0 ≤ (T ω : ℝ) * X.drift - X.X (T ω) ω := by
          simpa [X.X_zero ω] using hmono0
        linarith
      have hTreal : (T ω : ℝ) ≤ (H : ℝ) := by exact_mod_cast hTH ω
      have hmax : X.drift ≤ max 0 X.drift := le_max_right _ _
      have hmaxnonneg : 0 ≤ max 0 X.drift := le_max_left _ _
      have hres : (T ω : ℝ) * X.drift ≤
          (H : ℝ) * max 0 X.drift := calc
        (T ω : ℝ) * X.drift ≤ (T ω : ℝ) * max 0 X.drift :=
          mul_le_mul_of_nonneg_left hmax (NNReal.coe_nonneg _)
        _ ≤ (H : ℝ) * max 0 X.drift :=
          mul_le_mul_of_nonneg_right hTreal hmaxnonneg
      calc
        _ ≤ ENNReal.ofReal (rightLimit D (T ω) ω) :=
          avram_wave3_03_bv_stopped_payment_discounted_le_rightLimit
            q hq D hD ω (σ ω) (T ω)
        _ ≤ ENNReal.ofReal (x + (H : ℝ) * max 0 X.drift) :=
          ENNReal.ofReal_le_ofReal (by linarith)
    · exact zero_le
  letI : IsProbabilityMeasure P := X.isProbability
  calc
    _ ≤ (∫⁻ ω, ENNReal.ofReal (x + (H : ℝ) * max 0 X.drift) ∂P) :=
      lintegral_mono_ae hmajor
    _ = ENNReal.ofReal (x + (H : ℝ) * max 0 X.drift) := by simp
