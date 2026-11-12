-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger106_original_ruinclipped_strict_mass_le_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:11:03.705214+00:00
-- url     : https://prove2.me/submissions/39950518-5499-4238-8204-a0f2990d8375

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger96_measurable_stopped_cash_discount_lower_mass
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Stop-clipped original unweighted strict mass is controlled by discounted cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (n ρ : ℝ≥0) (hρn : ρ ≤ n)
    (hρruin : (ρ : ℝ≥0∞) ≤ ruinTime X x D ω) :
    (dividendMeasure D ω (Ioo (0 : ℝ) (ρ : ℝ))).toReal ≤
      Real.exp (q * (n : ℝ)) *
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hρreal : (ρ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hρn
  have hfin : (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ := by
    have hc := avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω (ruinTime X x D ω) n q hq
    apply lt_of_le_of_lt (lintegral_mono_set ?_) hc
    intro t ht
    exact ⟨ht.1, le_trans (le_of_lt ht.2) hρreal⟩
  let μ : Measure ℝ := dividendMeasure D ω
  let S : Set ℝ := Ioo (0 : ℝ) (ρ : ℝ)
  have hlow := avram_gledger96_measurable_stopped_cash_discount_lower_mass
    q hq μ S measurableSet_Ioo (ρ : ℝ) (by intro t ht; exact le_of_lt ht.2)
  have hcash : (∫⁻ t in S, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by
    apply lintegral_mono_set
    intro t ht
    have ht0 : 0 < t := ht.1
    have htReal : (t.toNNReal : ℝ) = t :=
      Real.coe_toNNReal t (le_of_lt ht0)
    have htNN : t.toNNReal < ρ := by
      exact_mod_cast (show (t.toNNReal : ℝ) < (ρ : ℝ) from by
        rw [htReal]
        exact ht.2)
    have htENN : (t.toNNReal : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_lt_of_le (by exact_mod_cast htNN) hρruin
    have htPay : t ∈ paymentTimes (ruinTime X x D ω) := by
      change 0 ≤ t ∧ (t = 0 ∨ ENNReal.ofReal t < ruinTime X x D ω)
      exact ⟨le_of_lt ht0, Or.inr (by
        change (t.toNNReal : ℝ≥0∞) < ruinTime X x D ω
        exact htENN)⟩
    exact ⟨htPay, ht.2⟩
  have hreal := ENNReal.toReal_mono (ne_of_lt hfin) (hlow.trans hcash)
  rw [ENNReal.toReal_ofReal_mul _ _ (le_of_lt (Real.exp_pos _))] at hreal
  have hreal' : (μ S).toReal * Real.exp (-(q * (ρ : ℝ))) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by
    simpa only [mul_comm] using hreal
  have hdiv := (le_div_iff₀ (Real.exp_pos (-(q * (ρ : ℝ))))).2 hreal'
  have hm : (μ S).toReal ≤ Real.exp (q * (ρ : ℝ)) *
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal := by
    simpa only [div_eq_mul_inv, Real.exp_neg, inv_inv, mul_comm] using hdiv
  have he : Real.exp (q * (ρ : ℝ)) ≤ Real.exp (q * (n : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hρreal hq)
  exact hm.trans (mul_le_mul_of_nonneg_right he ENNReal.toReal_nonneg)
