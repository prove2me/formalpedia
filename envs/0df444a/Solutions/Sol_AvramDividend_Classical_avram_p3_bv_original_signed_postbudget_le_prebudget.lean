-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_signed_postbudget_le_prebudget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:57:03.762759+00:00
-- url     : https://prove2.me/submissions/ffbd4770-a572-4250-b051-254dbb81d5c2

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_joint_horizon_terminal_accounting
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Unconditional original-process expectation comparison: the full stopped
    cash plus surviving postpayment value is bounded by the prepayment budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T, hT⟩
    let CashOpen : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let CashClosed : Ω → ℝ := fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    let Pre : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0
    let Post : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (x + X.X S ω - rightLimit D S ω)
      else 0
    (∫ ω, CashClosed ω + Post ω ∂P) ≤
      (∫ ω, CashOpen ω + Pre ω ∂P) := by
  dsimp only
  let S : ℝ≥0 := ⟨T, hT⟩
  have hpreI := avram_p3_bv_original_prebudget_L1
    X hBV x C D hD w hw_cont hw_neg q hq T hT
  have hc :=
    (avram_wave8_04_original_BV_full_cash_and_survival_terminal_L1
      X hBV q w hw_cont hw_neg x C D hD T hT).1
  have ht :=
    (avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
      X hBV q w C hC hw_cont hw0 hw_neg hw_smooth hw_grad
      x D hD T hT hTpos).1
  have hpostI := hc.add ht
  have hpath := avram_p3_bv_joint_horizon_terminal_accounting
    X x C D hD q w hjump T hT hTpos
  exact integral_mono_ae hpostI hpreI hpath
