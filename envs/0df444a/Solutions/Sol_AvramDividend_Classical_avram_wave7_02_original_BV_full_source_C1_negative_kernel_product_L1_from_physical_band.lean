-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:52:27.988747+00:00
-- url     : https://prove2.me/submissions/92b757be-e55f-4531-a6d9-67c23490eabb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
attribute [local instance] Classical.propDecidable
/-- Genuine stopped BV C1 original negative-jump product L1 with both candidate global value bound and predictable measurability discharged. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBandSmooth : Icc (a / 2) b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc (a / 2) b, ‖deriv w y‖₊ ≤ K)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ p, H p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0) :
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
  have hb : 0 ≤ b := (le_of_lt ha).trans hab
  obtain ⟨R, hR, hWnorm⟩ :=
    avram_wave7_02_original_C1_verification_candidate_uniform_below_finite_reserve_ceiling
      w hw_cont hw_neg b hb
  have hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R := by
    intro v hv
    simpa only [Real.norm_eq_abs] using hWnorm v hv
  have hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ (K : ℝ) * |u - v| :=
    avram_wave6_chat09_original_bv_C1_band_derivative_lipschitz
      X hBV C w (fun _ => hw_smooth) (a / 2) b
      hOpen hBandSmooth K hK
  have hHm : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      AEStronglyMeasurable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    have hHfun : H = (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        if p.1 ∈ E ∧ p.2 < 0 then
          Real.exp (-(q * (p.1.1 : ℝ))) *
            (w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
             w (Function.leftLim (fun s : ℝ≥0 =>
              x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
        else 0) := funext hH
    rw [hHfun]
    exact
      (avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
        X x D hD w hw_cont hw_neg q E hEm).aestronglyMeasurable
  exact
    avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
      X hBV x D w q hq a b (K : ℝ) R ha ha2 hab
      (NNReal.coe_nonneg K) hR hLip hWbound
      μ hμ E hEregion hMass H hH hHm
