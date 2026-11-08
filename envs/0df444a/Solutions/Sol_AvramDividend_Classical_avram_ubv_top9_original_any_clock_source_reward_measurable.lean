-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_any_clock_source_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:47:52.629973+00:00
-- url     : https://prove2.me/submissions/ba7da9ab-5c1d-479b-9ec9-0bf78867a7e1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Measurability of exact original stopped payoff, including right atoms. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    Measurable F := by
  let W : Ω → ℝ := fun ω =>
    if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
    else riskProcess X x D (ρ ω) ω
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Term : Ω → ℝ := fun ω => Real.exp (-(q * (ρ ω : ℝ))) * w (W ω)
  have hρmeas : Measurable (fun ω : Ω => (ρ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable ρ hρstop
  have hWmeas : Measurable W :=
    avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
      X x D hD ρ hρstop W (by intro ω; rfl)
  have hwmeas : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  have hExp : Measurable (fun ω : Ω => Real.exp (-(q * (ρ ω : ℝ)))) :=
    Real.measurable_exp.comp ((measurable_const.mul hρmeas).neg)
  have hTerm : Measurable Term := hExp.mul (hwmeas.comp hWmeas)
  have hCashENN : Measurable (fun ω : Ω =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) :=
    avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD q (fun ω => (ρ ω : ℝ)) hρmeas
  have hCash : Measurable Cash := ENNReal.measurable_toReal.comp hCashENN
  have hEq : F = (fun ω => Term ω + Cash ω) := by
    funext ω
    exact hFsource ω
  rw [hEq]
  exact hTerm.add hCash
