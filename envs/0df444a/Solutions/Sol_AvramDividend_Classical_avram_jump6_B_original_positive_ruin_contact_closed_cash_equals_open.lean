-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_positive_ruin_contact_closed_cash_equals_open
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:02:24.440628+00:00
-- url     : https://prove2.me/submissions/b99d08e2-2fac-47b2-b22c-d1a41060b9e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ η, τ η =
      (min (ruinTime X x D η) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k η, σ k η ≤ τ η)
    (k : ℕ) (ω : Ω)
    (hPos : σ k ω ≠ 0)
    (hContact : (σ k ω : ℝ≥0∞) = ruinTime X x D ω) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ s in Ico (0 : ℝ) (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal := by
  have hle : ∀ η, (σ k η : ℝ≥0∞) ≤ ruinTime X x D η := by
    intro η
    calc
      (σ k η : ℝ≥0∞) ≤ (τ η : ℝ≥0∞) := by exact_mod_cast hσle k η
      _ = min (ruinTime X x D η) (n : ℝ≥0∞) :=
        avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
          X x D n τ hτeq η
      _ ≤ ruinTime X x D η := min_le_left _ _
  have h :=
    avram_p4_d_dividend_original_all_random_stop_cash_zero_closed_or_ruin_open
      X x q D hD.1.1 (σ k)
      (fun η =>
        (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iic (σ k η : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D η)).toReal)
      (by intro η; rfl) hle ω
  have hn : ¬ ((σ k ω : ℝ≥0∞) < ruinTime X x D ω) := by
    rw [← hContact]
    exact lt_irrefl _
  simpa only [if_neg hPos, if_neg hn] using h
