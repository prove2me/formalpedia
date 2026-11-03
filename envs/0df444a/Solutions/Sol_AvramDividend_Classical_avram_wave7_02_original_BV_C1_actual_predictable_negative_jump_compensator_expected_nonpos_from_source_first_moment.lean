-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_BV_C1_actual_predictable_negative_jump_compensator_expected_nonpos_from_source_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:26.692065+00:00
-- url     : https://prove2.me/submissions/79720faf-d94f-4548-82ac-d5be1f460a78

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- Actual original BV C1 physical negative Levy-mark compensation is L1
and nonpositive in expectation from finite first variation and local C1 bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ v : ℝ, v < 0 → w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (q x : ℝ) (hq : 0 ≤ q) (D : ℝ≥0 → Ω → ℝ)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
    (hab : a ≤ b) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (hCapBand : Icc a b ⊆
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (E : Set (ℝ≥0 × Ω))
    (hEstrip : ∀ p ∈ E,
      Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hMass : X.ν (Iic (-a / 2)) < ⊤)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
        (w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
         w (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0)
    (hGMeas : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))] G) :
    Integrable (fun ω => ∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P ∧
    (∫ ω, (∫ t, ∫ z, G ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) ∂P) ≤ 0 := by
  have hEregion : ∀ p ∈ E,
      0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C := by
    intro p hp
    exact hCapBand (hEstrip p hp)
  have hGInt : ∀ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ →
      (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
        Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    intro μ hμ
    have hHm : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
        𝓕.rightCont.predictable;
        AEStronglyMeasurable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
      letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      exact hGMeas.aestronglyMeasurable
    exact avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
      X hBV x D w q hq a b L R ha ha2 hab hL hR hLip hWbound
      μ hμ E hEstrip hMass G hG hHm
  exact avram_wave7_02_original_BV_C1_stopped_negative_mark_random_compensator_L1_nonpositive_mean
    X hBV T C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
    q x D E hEregion G hG hGMeas hGInt
