-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_pathwise_signed_stieltjes_integrability_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:05:25.643252+00:00
-- url     : https://prove2.me/submissions/c923217f-836f-4dd6-b88d-dd594c440e40

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_unrestricted_discounted_stieltjes_antitone_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Genuine unrestricted signed Stieltjes integrability transfers from a
    smaller to a larger discount at each original source sample path. -/
/- Fresh proof snapshot following earlier terminal storage rejection. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q₁ q₂ : ℝ) (hq : q₁ ≤ q₂)
    (ω : Ω)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q₁ * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    IntegrableOn (fun t : ℝ => Real.exp (-(q₂ * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω) := by
  have hcash1 :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₁ * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    (avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
      X x D hD ω q₁).2 hInt
  have hcash2 :
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q₂ * t)))
          ∂(dividendMeasure D ω)) < ⊤ :=
    lt_of_le_of_lt
      (avram_wave7_03_original_full_unrestricted_discounted_stieltjes_antitone_rate
        D ω (ruinTime X x D ω) q₁ q₂ hq) hcash1
  exact
    (avram_wave7_03_pathwise_original_full_cash_finite_iff_signed_stieltjes_integrable
      X x D hD ω q₂).1 hcash2
