-- Prove2me | solution 1 for AvramDividend.Classical.capped_hjb_discounted_payment_weighted_interior_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:01:43.436981+00:00
-- url     : https://prove2.me/submissions/6c1522d9-9a76-4dcc-af58-6369c4db3c60

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_payment_interior_boundary_lintegral_split
import Theorems.Thm_AvramDividend_Classical_hjb_component_inequalities
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The exact stopped Stieltjes payout is controlled by the HJB derivative-weighted payment on the strictly interior reserve region plus the full residual boundary payment. This includes diffuse and atomic dividend mass and requires no integrability assumption on the weighted ENNReal integrand. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ω : Ω) (u : ℝ → ℝ)
    (hInterior : MeasurableSet
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) ∩
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u t))
        ∂(dividendMeasure D ω)) +
    (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) \
      {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let A : Set ℝ := (paymentTimes σ ∩ Iic (T : ℝ)) ∩
    {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C}
  have hA : MeasurableSet A :=
    ((paymentTimes_measurable σ).inter measurableSet_Iic).inter hInterior
  have hmono :
      (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in A,
        ENNReal.ofReal (Real.exp (-(q * t)) * deriv w (u t))
          ∂(dividendMeasure D ω)) := by
    apply MeasureTheory.lintegral_mono_ae
    filter_upwards [MeasureTheory.ae_restrict_mem hA] with t ht
    obtain ⟨_, htI⟩ := ht
    obtain ⟨_, _, hderiv⟩ :=
      hjb_component_inequalities X q w C hw_hjb (u t) htI.1 htI.2
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left hderiv
      (le_of_lt (Real.exp_pos (-(q * t))))
    simpa using h
  have hsplit :=
    discounted_dividend_payment_interior_boundary_lintegral_split
      D hD σ T ω C u hInterior
      (fun t => ENNReal.ofReal (Real.exp (-(q * t))))
  calc
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) +
        (∫⁻ t in (paymentTimes σ ∩ Iic (T : ℝ)) \
          {t : ℝ | 0 < u t ∧ ENNReal.ofReal (u t) < C},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
          simpa only [A] using hsplit
    _ ≤ _ := add_le_add hmono le_rfl
