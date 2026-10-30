-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_surviving_random_clock_drift_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:28:36.798788+00:00
-- url     : https://prove2.me/submissions/98aa11ba-5046-41ba-9638-235e086c0e78

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

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
    ∀ᵐ ω ∂P, (S : ℝ≥0∞) < ruinTime X x D ω →
      (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + (S : ℝ) * X.drift) := by
  filter_upwards [bv_actual_levy_residual_ae_monotone_all_times X hBV] with ω hω
  intro hSurv
  have hmono :
      (0 : ℝ) * X.drift - X.X 0 ω ≤
        (S : ℝ) * X.drift - X.X S ω :=
        hω (show (0 : ℝ≥0) ≤ S from zero_le)
  have hX : X.X S ω ≤ (S : ℝ) * X.drift := by
    have hnonneg : 0 ≤ (S : ℝ) * X.drift - X.X S ω := by
      simpa [X.X_zero ω] using hmono
    linarith
  calc
    (∫⁻ r in paymentTimes (σ ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * r))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (x + X.X S ω) :=
        stopped_dividend_payoff_le_uncontrolled_reserve_before_ruin
          X x D hD ω q hq (σ ω) T S hTS hSurv
    _ ≤ ENNReal.ofReal (x + (S : ℝ) * X.drift) :=
      ENNReal.ofReal_le_ofReal (by linarith)
