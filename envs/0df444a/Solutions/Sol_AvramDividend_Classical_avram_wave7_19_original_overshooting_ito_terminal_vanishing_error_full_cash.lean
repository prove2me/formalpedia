-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_overshooting_ito_terminal_vanishing_error_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:38:10.485587+00:00
-- url     : https://prove2.me/submissions/2b7a9d16-4f00-4922-a355-305de9fbb6a6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_liminf_clock_full_expected_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Overshooting nonmonotone clocks retain full original cash after terminal/error removal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminfLower : ∀ᵐ ω ∂P,
      ruinTime X x D ω ≤ (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω))
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ (n : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal ε n ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  apply avram_wave7_19_original_overshooting_liminf_clock_full_expected_cash_budget
    X q x T D hD τ hτmeas hLiminfLower budget
  intro n
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hbudget
  calc
    (∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
        (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
          Terminal ε n ω) ∂P) := by
      apply lintegral_mono
      intro ω
      calc
        (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
            (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
              ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + 0 :=
            (add_zero _).symm
        _ ≤ _ := add_le_add_right (bot_le : (0 : ℝ≥0∞) ≤ Terminal ε n ω) _
    _ ≤ budget + ENNReal.ofNNReal ε := hStopped n ε hε hbudget
