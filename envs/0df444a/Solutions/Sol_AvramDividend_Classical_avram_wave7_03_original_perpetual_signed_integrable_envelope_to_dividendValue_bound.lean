-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_perpetual_signed_integrable_envelope_to_dividendValue_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:51:00.822252+00:00
-- url     : https://prove2.me/submissions/d3c42721-ad7b-482b-b1f6-db3a87abf478

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- An integrable original perpetual signed Stieltjes cash envelope controls
    the exact original Lévy strategy value, including the initial right atom
    and all continuous strictly pre-ruin payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (B : Ω → ℝ) (K : ℝ)
    (hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω))
        (dividendMeasure D ω))
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    dividendValue X q x D ≤ ENNReal.ofReal K := by
  have hBPos : 0 ≤ᵐ[P] B := by
    filter_upwards [hSignedBound] with ω hb
    have hCashPos :
        0 ≤ (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) :=
      integral_nonneg (fun t => (Real.exp_pos (-(q * t))).le)
    exact le_trans hCashPos hb
  have hCashBound : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal (B ω) := by
    filter_upwards [hIntCash, hSignedBound] with ω hωInt hωBound
    have hPos :
        0 ≤ᵐ[(dividendMeasure D ω).restrict
          (paymentTimes (ruinTime X x D ω))]
          (fun t : ℝ => Real.exp (-(q * t))) :=
      Filter.Eventually.of_forall
        (fun t => (Real.exp_pos (-(q * t))).le)
    calc
      (∫⁻ t in paymentTimes (ruinTime X x D ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) =
        ENNReal.ofReal
          (∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) :=
          (ofReal_integral_eq_lintegral_ofReal hωInt hPos).symm
      _ ≤ ENNReal.ofReal (B ω) :=
        ENNReal.ofReal_le_ofReal hωBound
  change (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
    ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (B ω) ∂P) :=
      lintegral_mono_ae hCashBound
    _ = ENNReal.ofReal (∫ ω, B ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hBInt hBPos).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hBMean
