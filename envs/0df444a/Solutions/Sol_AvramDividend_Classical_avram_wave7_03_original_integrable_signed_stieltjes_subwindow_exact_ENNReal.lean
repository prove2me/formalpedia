-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_integrable_signed_stieltjes_subwindow_exact_ENNReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:37:18.709615+00:00
-- url     : https://prove2.me/submissions/b07a0692-cbd9-4bba-a3e1-88e63dfe8bbb

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Any true original payment subwindow converts exactly from genuine signed
    real Stieltjes cash to ENNReal, including time-zero and continuous payouts. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q : ℝ)
    (hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω))
    (S : Set ℝ) (hS : S ⊆ paymentTimes (ruinTime X x D ω)) :
    (∫⁻ t in S,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    ENNReal.ofReal
      (∫ t in S, Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  have hSubInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t))) S
      (dividendMeasure D ω) :=
    hInt.mono_set hS
  have hPos :
      0 ≤ᵐ[(dividendMeasure D ω).restrict S]
        (fun t : ℝ => Real.exp (-(q * t))) :=
    Filter.Eventually.of_forall (fun t => (Real.exp_pos (-(q * t))).le)
  exact (ofReal_integral_eq_lintegral_ofReal hSubInt hPos).symm
