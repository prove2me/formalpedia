-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_predictable_compensator_nonpositive_mean_from_physical_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:01:53.042964+00:00
-- url     : https://prove2.me/submissions/337ad0da-25fa-465d-a9e5-4d4a9cb2d202

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Exact source predictable negative-mark compensator sign with automatic physical C1 product integrability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C → 1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hOpen : IsOpen {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hBandSmooth : Icc (a / 2) b ⊆ {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (K : ℝ≥0) (hK : ∀ v ∈ Icc (a / 2) b, ‖deriv w v‖₊ ≤ K)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEband : ∀ p ∈ E, Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hEregion : ∀ p ∈ E,
      0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0) :
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  have hGfun : G = (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim (fun s : ℝ≥0 =>
            x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) else 0) :=
    funext hG
  have hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G := by
    rw [hGfun]
    exact avram_wave7_17_original_stopped_predictable_discounted_negative_jump_kernel_measurable
      X x D hD w hw_cont hw_neg q E hEm
  have hGInt : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    intro μ hμ
    exact
      avram_wave7_02_original_BV_full_source_C1_negative_kernel_product_L1_from_physical_band
        X hBV x D hD C w hw_cont hw_neg hw_smooth q hq
        a b ha ha2 hab hOpen hBandSmooth K hK μ hμ hMass
        E hEm hEband G hG
  exact
    avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
      X hBV T C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      q x D E hEregion G hG hGMeas hGInt
