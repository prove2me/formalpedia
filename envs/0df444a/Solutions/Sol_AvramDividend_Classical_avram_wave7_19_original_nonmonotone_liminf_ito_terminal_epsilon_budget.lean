-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_nonmonotone_liminf_ito_terminal_epsilon_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:39:02.999652+00:00
-- url     : https://prove2.me/submissions/da426485-410f-458b-948b-d9669f19df66

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original nonmonotone stopped Ito terminal and truncation errors vanish at ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n : ℕ, Measurable (τ n))
    (hLiminf : ∀ᵐ ω ∂P,
      (⨆ n : ℕ, ⨅ k : ℕ, τ (n + k) ω) = ruinTime X x D ω)
    (Terminal : NNReal → ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ (n : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
        Terminal ε n ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  apply avram_wave7_19_original_nonmonotone_liminf_clock_full_expected_cash_budget
    X q x T D hD τ hτmeas hLiminf budget
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
