-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_closed_cash_L1_of_integrable_F
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T23:40:12.926639+00:00
-- url     : https://prove2.me/submissions/cd18ce7a-5c8d-4033-bd8d-28684e5bfec8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source reward controls its full original closed Stieltjes cash in L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : Integrable F P) :
    Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P := by
  let W : Ω → ℝ := fun ω =>
    if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω
    then x + X.X (σ ω) ω - rightLimit D (σ ω) ω
    else riskProcess X x D (σ ω) ω
  let Term : Ω → ℝ :=
    fun ω => Real.exp (-(q * (σ ω : ℝ))) * w (W ω)
  let Cash : Ω → ℝ := fun ω =>
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  have hTermNN : ∀ ω, 0 ≤ Term ω :=
    avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
      X hBV w C hC hw0 hw_cont hw_neg hw_smooth hw_grad
      x hxc D hD q σ W Term (by intro ω; rfl) (by intro ω; rfl)
  have hσmeas : Measurable (fun ω : Ω => (σ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
      σ hσstop
  have hCashENN : Measurable (fun ω : Ω =>
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)) :=
    avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hD.1.1 q (fun ω => (σ ω : ℝ)) hσmeas
  have hCashMeas : AEStronglyMeasurable Cash P :=
    (ENNReal.measurable_toReal.comp hCashENN).aestronglyMeasurable
  have hCashNN : ∀ᵐ ω ∂P, 0 ≤ Cash ω := by
    filter_upwards [] with ω
    exact ENNReal.toReal_nonneg
  have hCashLe : ∀ᵐ ω ∂P, Cash ω ≤ F ω := by
    filter_upwards [] with ω
    have hT := hTermNN ω
    have hEq : F ω = Term ω + Cash ω := hFsource ω
    linarith
  exact hFI.mono_nonneg hCashMeas hCashNN hCashLe
