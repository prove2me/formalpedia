-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top9_original_any_compact_clock_closed_cash_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:07:41.812672+00:00
-- url     : https://prove2.me/submissions/9c40a6d2-e2c6-4d81-ae36-178af9338b57

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f15_continuous_zero_negative_uniform_bounded_above
import Theorems.Thm_AvramDividend_Classical_avram_f18_original_stopped_postpayment_reserve_upper_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source-exact compact-clock L1 for original post-right terminal and closed Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ ρ : Ω → ℝ≥0) (hρle : ∀ ω, ρ ω ≤ τ ω)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρmeas : Measurable (fun ω => (ρ ω : ℝ)))
    (hCashτI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P)
    (K : ℝ) (hXBound : ∀ ω, X.X (ρ ω) ω ≤ K)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (ρ ω : ℝ))) *
        w (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
          else riskProcess X x D (ρ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    Integrable F P := by
  let Wloc : Ω → ℝ := fun ω =>
    if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
    else riskProcess X x D (ρ ω) ω
  let Cloc : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let Tloc : Ω → ℝ := fun ω =>
    Real.exp (-(q * (ρ ω : ℝ))) * w (Wloc ω)
  have hwm : Measurable w :=
    avram_p4_c_generator_zero_negative_payoff_measurable w hw_cont hw_neg
  obtain ⟨B, hBnn, hB⟩ :=
    avram_f15_continuous_zero_negative_uniform_bounded_above w hw_cont hw_neg (x + K)
  have hWB : ∀ ω, |w (Wloc ω)| ≤ B := by
    intro ω
    apply hB
    exact avram_f18_original_stopped_postpayment_reserve_upper_bound
      X x D hD.1.1 ω (ρ ω) K (hXBound ω)
  have hWM : Measurable Wloc :=
    avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
      X x D hD.1.1 ρ hρstop Wloc (by intro ω; rfl)
  have hTimeExp : Measurable
      (fun ω : Ω => Real.exp (-(q * (ρ ω : ℝ)))) :=
    Real.measurable_exp.comp ((measurable_const.mul hρmeas).neg)
  have hTM : Measurable Tloc := hTimeExp.mul (hwm.comp hWM)
  have hTI : Integrable Tloc P :=
    avram_p4_e_localise_discounted_terminal_integrable_of_ae_bound
      X q hq ρ w Wloc hTM.aestronglyMeasurable B
      (Filter.Eventually.of_forall hWB)
  have hCI : Integrable Cloc P :=
    avram_ubv_loc6_original_ordered_clocks_closed_cash_L1
      X x q hq C D hD ρ τ hρle hρmeas hCashτI
  have hFeq : F = (fun ω => Tloc ω + Cloc ω) := by
    funext ω
    exact hFsource ω
  rw [hFeq]
  exact hTI.add hCI
