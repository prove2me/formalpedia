-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger105_original_clipped_strict_strip_le_real_strip
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:02:55.361906+00:00
-- url     : https://prove2.me/submissions/a1d70081-d195-4a9e-9cfe-66c4f7f1ac86

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger84_original_strict_final_cell_cash_mono
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Real subtraction adds at most the original nonnegative payment-time atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n ρ δ : ℝ≥0) (hρn : ρ ≤ n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((ρ - δ : ℝ≥0) : ℝ) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hlow : (ρ : ℝ) - (δ : ℝ) ≤ ((ρ - δ : ℝ≥0) : ℝ) := by
    by_cases hd : δ ≤ ρ
    · rw [NNReal.coe_sub hd]
    · have hz : ρ - δ = 0 := tsub_eq_zero_of_le (le_of_not_ge hd)
      rw [hz]
      have hh : (ρ : ℝ) ≤ (δ : ℝ) := by exact_mod_cast le_of_not_ge hd
      simpa using sub_nonpos.mpr hh
  have hmono := avram_gledger84_original_strict_final_cell_cash_mono
    X x D ω q ρ δ (ρ - δ) hlow tsub_le_self
  have hfin : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
      Ioo ((ρ : ℝ) - (δ : ℝ)) (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
    have hc := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω (ruinTime X x D ω) n q hq
    apply lt_of_le_of_lt (lintegral_mono_set ?_) hc
    intro t ht
    have hρreal : (ρ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hρn
    exact ⟨ht.1, le_trans (le_of_lt ht.2.2) hρreal⟩
  exact ENNReal.toReal_mono (ne_of_lt hfin) hmono
