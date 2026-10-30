-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_surviving_expected_stieltjes_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:31:05.067898+00:00
-- url     : https://prove2.me/submissions/56a3979c-7b4a-49c4-9c55-70349bc1b58b

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_surviving_stopped_dividend_expected_le_uncontrolled_reserve
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0∞)
    (T S : ℝ≥0) (hTS : T < S) :
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
    ENNReal.ofReal (x + (S : ℝ) * X.drift) := by
  have hX : ∀ᵐ ω ∂P,
      ENNReal.ofReal (x + X.X S ω) ≤
        ENNReal.ofReal (x + (S : ℝ) * X.drift) := by
    filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV]
      with ω hω
    have hmono :
        (0 : ℝ) * X.drift - X.X 0 ω ≤
          (S : ℝ) * X.drift - X.X S ω :=
      hω (show (0 : ℝ≥0) ≤ S from zero_le)
    have hnonneg : 0 ≤ (S : ℝ) * X.drift - X.X S ω := by
      simpa [X.X_zero ω] using hmono
    exact ENNReal.ofReal_le_ofReal (by linarith)
  letI : IsProbabilityMeasure P := X.isProbability
  calc
    (∫⁻ ω, if (S : ℝ≥0∞) < ruinTime X x D ω then
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω))
      else 0 ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (x + X.X S ω) ∂P) :=
      surviving_stopped_dividend_expected_le_uncontrolled_reserve
        X x D hD q hq σ T S hTS
    _ ≤ (∫⁻ ω, ENNReal.ofReal (x + (S : ℝ) * X.drift) ∂P) :=
      lintegral_mono_ae hX
    _ = ENNReal.ofReal (x + (S : ℝ) * X.drift) := by simp
