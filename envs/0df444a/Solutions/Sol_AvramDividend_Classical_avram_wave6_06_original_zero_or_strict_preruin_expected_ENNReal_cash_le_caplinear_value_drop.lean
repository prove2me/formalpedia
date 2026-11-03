-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_zero_or_strict_preruin_expected_ENNReal_cash_le_caplinear_value_drop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T10:57:07.156168+00:00
-- url     : https://prove2.me/submissions/f2eff105-c3b9-40d7-ae2d-674ea1b33932

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Actual original double-ENNReal expected stopped cash is dominated
    by the conull source caplinear value loss; no stochastic identity needed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hPre : ∀ᵐ ω ∂P, τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ ω,
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∂P) ≤
    (∫⁻ ω,
      ENNReal.ofReal
        (V (x + X.X (τ ω) ω) -
         V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω)) ∂P) := by
  apply lintegral_mono_ae
  filter_upwards [hPre] with ω hω
  exact
    avram_wave6_06_original_zero_or_strict_preruin_stopped_ENNReal_cash_le_caplinear_value_drop
      X x C q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω τ hω
