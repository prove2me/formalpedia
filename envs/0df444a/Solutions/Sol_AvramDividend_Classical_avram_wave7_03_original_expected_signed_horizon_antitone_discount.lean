-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_expected_signed_horizon_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:26:24.400134+00:00
-- url     : https://prove2.me/submissions/6319f514-dfbf-411e-b2d5-235c97a62006

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Under actual outer L1 assumptions, the original expected signed
    finite-horizon source Stieltjes cash decreases with the discount rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (T : ℝ)
    (hfinite : ∀ᵐ ω ∂P, (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ≠ ⊤)
    (hInt₁ : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) P)
    (hInt₂ : Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) P) :
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) ∂P) ≤
    (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) ∂P) := by
  apply MeasureTheory.integral_mono_ae hInt₂ hInt₁
  filter_upwards [hfinite] with ω hω
  exact avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount
    X x D ω q₁ q₂ hq₁ hq T hω
