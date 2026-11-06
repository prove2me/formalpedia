-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_tail_cofinal_vanishing_closed_cash_real_perpetual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:45:50.225205+00:00
-- url     : https://prove2.me/submissions/d2234017-5675-4564-95b5-c31a37e4dfcd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Tail-cofinal original closed horizons with vanishing budgets control
    perpetual value and the actual signed real payout, including atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ)
    (hTail : ∀ (N : ℕ) (a : ℝ), ∃ k : ℕ, N ≤ k ∧ a ≤ T k)
    (B : ℝ≥0∞) (hB : B < ⊤)
    (error : ℕ → ℝ≥0∞)
    (hError : ∀ ε : ℝ≥0, 0 < ε →
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → error k ≤ (ε : ℝ≥0∞))
    (hBudget : ∀ k : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
      (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B + error k) :
    dividendValue X q x D ≤ B ∧
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
    dividendValue X q x D =
      ENNReal.ofReal (∫ ω,
        (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by
  classical
  let cash : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P
  have hEach (n : ℕ) : cash n ≤ B := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨N, hN⟩ := hError ε hε
    obtain ⟨k, hNk, hTk⟩ := hTail N (n : ℝ)
    obtain ⟨Terminal, hTerminal⟩ := hBudget k
    calc
      cash n ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) := by
          dsimp [cash]
          apply lintegral_mono
          intro ω
          apply lintegral_mono_set
          intro t ht
          exact ⟨ht.1, le_trans ht.2 hTk⟩
      _ ≤ (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (T k),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) + Terminal ω) ∂P) := by
          apply lintegral_mono
          intro ω
          exact le_add_of_nonneg_right bot_le
      _ ≤ B + error k := hTerminal
      _ ≤ B + (ε : ℝ≥0∞) := add_le_add_right (hN k hNk) B
  have hValue : dividendValue X q x D ≤ B := by
    rw [dividendValue_eq_iSup_truncated X q x D hD]
    change (⨆ n : ℕ, cash n) ≤ B
    exact iSup_le hEach
  have hFinite : dividendValue X q x D < ⊤ :=
    lt_of_le_of_lt hValue hB
  obtain ⟨hL1, hExact⟩ :=
    avram_wave7_03_original_perpetual_signed_stieltjes_L1_and_exact_outer_mean_of_finite
      X x D hD.1 q hFinite
  exact ⟨hValue, hL1, hExact⟩
