-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_strategywise_mean_vanishing_random_error_strict_real_values
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:50:51.952676+00:00
-- url     : https://prove2.me/submissions/89c0044a-31e8-4659-bffe-86e4c8e11291

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_vanishing_strict_terminal_real_values

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Strategywise original random errors with vanishing means imply real
    payout bounds for capped and unrestricted dividends (strict horizons). -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ error : ℕ → Ω → ℝ≥0∞,
          (∀ ε : ℝ≥0, 0 < ε →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              (∫⁻ ω, error n ω ∂P) ≤ (ε : ℝ≥0∞)) ∧
          (∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iio (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
              ENNReal.ofReal (w x) + (∫⁻ ω, error n ω ∂P))) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal (∫ ω,
            (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
  have hScalar : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ error : ℕ → ℝ≥0∞,
          (∀ ε : ℝ≥0, 0 < ε →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              error n ≤ (ε : ℝ≥0∞)) ∧
          (∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iio (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
              ENNReal.ofReal (w x) + error n) := by
    intro x hx hxc D hD
    obtain ⟨error, hError, hBudget⟩ := hSource x hx hxc D hD
    exact ⟨(fun n => ∫⁻ ω, error n ω ∂P), hError, hBudget⟩
  exact avram_limit2_strategywise_vanishing_strict_terminal_real_values X q w C hw hScalar
