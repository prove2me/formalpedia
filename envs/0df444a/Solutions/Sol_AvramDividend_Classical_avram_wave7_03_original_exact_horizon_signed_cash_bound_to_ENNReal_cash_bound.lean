-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_exact_horizon_signed_cash_bound_to_ENNReal_cash_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:37:30.946468+00:00
-- url     : https://prove2.me/submissions/572466e6-44c2-434e-8d0b-5d86bce2cf48

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

/-- An actual signed pathwise original dividend Stieltjes upper budget
    transfers to exact ENNReal payment cash at the identical horizon,
    with an explicit finite signed integrability hypothesis. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q T B : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω) ∩ Iic T)
      (dividendMeasure D ω))
    (hSigned :
      (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ≤ B) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≤ ENNReal.ofReal B := by
  have hPos :
      0 ≤ᵐ[(dividendMeasure D ω).restrict
        (paymentTimes (ruinTime X x D ω) ∩ Iic T)]
        (fun t : ℝ => Real.exp (-(q * t))) :=
    Filter.Eventually.of_forall
      (fun t => (Real.exp_pos (-(q * t))).le)
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) :=
        (ofReal_integral_eq_lintegral_ofReal hInt hPos).symm
    _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hSigned
