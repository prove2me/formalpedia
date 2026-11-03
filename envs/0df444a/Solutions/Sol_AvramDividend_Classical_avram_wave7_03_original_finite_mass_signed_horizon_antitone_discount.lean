-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_mass_signed_horizon_antitone_discount
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:17:11.182206+00:00
-- url     : https://prove2.me/submissions/ed432ac7-3c1b-4ac8-8232-6d13186c1bec

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Finite original Stieltjes mass makes the real discounted rewards
    integrable, so their original signed Lebesgue integrals respect discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq : q₁ ≤ q₂) (T : ℝ)
    (hfinite : (dividendMeasure D ω)
      (paymentTimes (ruinTime X x D ω) ∩ Iic T) ≠ ⊤) :
    (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω)) := by
  let A : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic T
  have hA : MeasurableSet A :=
    (paymentTimes_measurable _).inter measurableSet_Iic
  have hnonneg : ∀ t ∈ A, 0 ≤ t := fun t ht => ht.1.1
  have hq₂ : 0 ≤ q₂ := le_trans hq₁ hq
  have hInt₂ : IntegrableOn (fun t : ℝ => Real.exp (-(q₂ * t)))
      A (dividendMeasure D ω) :=
    discounted_stieltjes_integrableOn_of_finite_measure
      q₂ hq₂ (dividendMeasure D ω) A hA hnonneg hfinite
  have hInt₁ : IntegrableOn (fun t : ℝ => Real.exp (-(q₁ * t)))
      A (dividendMeasure D ω) :=
    discounted_stieltjes_integrableOn_of_finite_measure
      q₁ hq₁ (dividendMeasure D ω) A hA hnonneg hfinite
  change (∫ t in A, Real.exp (-(q₂ * t)) ∂(dividendMeasure D ω)) ≤
    (∫ t in A, Real.exp (-(q₁ * t)) ∂(dividendMeasure D ω))
  apply MeasureTheory.integral_mono_ae hInt₂ hInt₁
  filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
  have ht0 : 0 ≤ t := hnonneg t ht
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hq ht0))
