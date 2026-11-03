-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_random_clock_integrable_signed_envelope_to_exact_expected_ENNReal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:38:44.461004+00:00
-- url     : https://prove2.me/submissions/48da9c69-ee15-4576-831a-6d2279888684

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

/-- Actual source signed pathwise Stieltjes budgets together with genuine
    integrable nonnegative real terminal envelopes imply the exact outer
    original-process double ENNReal expected dividend budget. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ B : Ω → ℝ) (K : ℝ)
    (hIntCash : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω))
        (dividendMeasure D ω))
    (hSignedBound : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω)
    (hBInt : Integrable B P)
    (hBPos : 0 ≤ᵐ[P] B)
    (hBMean : (∫ ω, B ω ∂P) ≤ K) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal K := by
  have hCashBound : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal (B ω) := by
    filter_upwards [hIntCash, hSignedBound] with ω hωInt hωBound
    have hPos :
        0 ≤ᵐ[(dividendMeasure D ω).restrict
          (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω))]
          (fun t : ℝ => Real.exp (-(q * t))) :=
      Filter.Eventually.of_forall
        (fun t => (Real.exp_pos (-(q * t))).le)
    calc
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) =
        ENNReal.ofReal
          (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) :=
          (ofReal_integral_eq_lintegral_ofReal hωInt hPos).symm
      _ ≤ ENNReal.ofReal (B ω) :=
        ENNReal.ofReal_le_ofReal hωBound
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
      (∫⁻ ω, ENNReal.ofReal (B ω) ∂P) :=
      lintegral_mono_ae hCashBound
    _ = ENNReal.ofReal (∫ ω, B ω ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hBInt hBPos).symm
    _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal hBMean
