-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_ae_random_subwindow_ENNReal_toReal_eq_signed_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:37:54.927805+00:00
-- url     : https://prove2.me/submissions/5625b1aa-c8ef-44a2-898f-23ab1a5043a9

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

/-- Almost surely, genuine original Stieltjes cash on any true random
    payment subwindow has the exact signed real and ENNReal.toReal equality. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (S : Ω → Set ℝ)
    (hSub : ∀ᵐ ω ∂P, S ω ⊆ paymentTimes (ruinTime X x D ω))
    (hInt : ∀ᵐ ω ∂P, IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (paymentTimes (ruinTime X x D ω)) (dividendMeasure D ω)) :
    ∀ᵐ ω ∂P,
      (∫⁻ t in S ω, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal =
      (∫ t in S ω, Real.exp (-(q * t))
        ∂(dividendMeasure D ω)) := by
  filter_upwards [hSub, hInt] with ω hS hωInt
  have hSubInt : IntegrableOn
      (fun t : ℝ => Real.exp (-(q * t)))
      (S ω) (dividendMeasure D ω) :=
    hωInt.mono_set hS
  have hPos :
      0 ≤ᵐ[(dividendMeasure D ω).restrict (S ω)]
        (fun t : ℝ => Real.exp (-(q * t))) :=
    Filter.Eventually.of_forall (fun t => (Real.exp_pos (-(q * t))).le)
  have hEq :
      (∫⁻ t in S ω, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) =
      ENNReal.ofReal
        (∫ t in S ω, Real.exp (-(q * t))
          ∂(dividendMeasure D ω)) :=
    (ofReal_integral_eq_lintegral_ofReal hSubInt hPos).symm
  have hNonneg :
      0 ≤ (∫ t in S ω, Real.exp (-(q * t))
        ∂(dividendMeasure D ω)) :=
    integral_nonneg (fun t => (Real.exp_pos (-(q * t))).le)
  rw [hEq, ENNReal.toReal_ofReal hNonneg]
