-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_random_clock_ae_signed_budget_to_double_ENNReal_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:38:49.81375+00:00
-- url     : https://prove2.me/submissions/83b38374-c047-4f59-9503-32b9a3588c55

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

/-- The genuine random-clock signed pathwise Stieltjes budget implies
    the original outer ENNReal dividend expectation budget at the identical
    stopped payment set, under explicit almost-sure signed integrability. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (τ B : Ω → ℝ)
    (hInt : ∀ᵐ ω ∂P,
      IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
        (paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω))
        (dividendMeasure D ω))
    (hSigned : ∀ᵐ ω ∂P,
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ENNReal.ofReal (B ω) ∂P) := by
  apply lintegral_mono_ae
  filter_upwards [hInt, hSigned] with ω hωInt hωBound
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
    _ ≤ ENNReal.ofReal (B ω) := ENNReal.ofReal_le_ofReal hωBound
