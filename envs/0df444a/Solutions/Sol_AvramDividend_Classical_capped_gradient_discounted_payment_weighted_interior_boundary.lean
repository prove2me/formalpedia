-- Prove2me | solution 1 for AvramDividend.Classical.capped_gradient_discounted_payment_weighted_interior_boundary
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:30:36.810372+00:00
-- url     : https://prove2.me/submissions/90dac509-b44f-4ad2-974d-746764ae10d1

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_dividend_payment_interior_boundary_lintegral_split
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A lower bound on the candidate derivative alone controls actual dividends in the positive-reserve interior, while retaining all diffuse and atomic cap/zero-reserve boundary payments. This form applies to BV subsolutions without an HJB maximum equality. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
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
    apply ENNReal.ofReal_le_ofReal
    have h := mul_le_mul_of_nonneg_left
      (hw_grad (u t) htI.1 htI.2)
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
