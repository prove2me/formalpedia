-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_overshooting_diagonal_ito_terminal_asymptotic_error_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:55:35.318559+00:00
-- url     : https://prove2.me/submissions/0f4bf1c6-cc92-4f23-bf9d-65b5a20654ea

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_overshooting_diagonal_fatou_expected_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Eventual small-jump Ito errors suffice for a diagonal nonmonotone ruin-cash Fatou bound. -/
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
    (hStoppedTail : ∀ (ε : NNReal), 0 < ε → budget < ⊤ →
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∫⁻ ω, ((∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
          Terminal ε n ω) ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  let E (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ ω, (∫⁻ t in paymentTimes (τ n ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P
  have hBound : (⨆ m : ℕ, ⨅ k : ℕ, E (m + k)) ≤ budget := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε hbudget
    obtain ⟨N, hN⟩ := hStoppedTail ε hε hbudget
    apply iSup_le
    intro m
    calc
      (⨅ k : ℕ, E (m + k)) ≤ E (m + N) :=
        iInf_le (fun k : ℕ => E (m + k)) N
      _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (τ (m + N) ω) ∩ Iic T,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
          Terminal ε (m + N) ω) ∂P) := by
        dsimp [E]
        apply lintegral_mono
        intro ω
        calc
          (∫⁻ t in paymentTimes (τ (m + N) ω) ∩ Iic T,
            ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
              (∫⁻ t in paymentTimes (τ (m + N) ω) ∩ Iic T,
                ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) + 0 :=
              (add_zero _).symm
          _ ≤ _ := add_le_add_right
            (bot_le : (0 : ℝ≥0∞) ≤ Terminal ε (m + N) ω) _
      _ ≤ budget + ENNReal.ofNNReal ε := hN (m + N) (by omega)
  exact avram_wave7_19_original_overshooting_diagonal_fatou_expected_cash_budget
    X q x T D hD τ hτmeas hLiminfLower budget hBound
