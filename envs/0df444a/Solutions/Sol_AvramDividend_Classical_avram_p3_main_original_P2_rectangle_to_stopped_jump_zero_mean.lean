-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_main_original_P2_rectangle_to_stopped_jump_zero_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:52:36.368554+00:00
-- url     : https://prove2.me/submissions/d97a6e96-fcb3-4089-bc9f-9aae16e82c07

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_P2_intrinsic_fully_constructed_stopped_signed_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- The source P2 rectangle identity directly centres the actual intrinsic
stopped BV C1 jump, using the accepted P3-B predictable-clock construction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (T : ℝ≥0) (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
    (hτ : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ) (hq : 0 ≤ q)
    (a b L R : ℝ) (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
      |w u - w v| ≤ L * |u - v|)
    (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ∈ Icc a b)
    (hν : (∫⁻ z : ℝ, ENNReal.ofReal (min (1 : ℝ) (z ^ 2)) ∂X.ν) < ⊤)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hG : ∀ p, G p = if p.1 ∈ E ∧ p.2 < 0 then
      Real.exp (-(q * (p.1.1 : ℝ))) *
      (w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
        rightLimit D s p.1.2) p.1.1 + p.2) -
       w (Function.leftLim (fun s : ℝ≥0 => x + X.X s p.1.2 -
        rightLimit D s p.1.2) p.1.1)) else 0)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0) :
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal))) ∂P) = 0 := by
  have hP2 : ∀ (s t : ℝ≥0), s ≤ t → ∀ (A : Set Ω),
      MeasurableSet[𝓕 s] A → ∀ (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω in A, NX ω (Ioc s t ×ˢ B) ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro s t hst A hA B hB
    simpa only [hNX] using
      (avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
        X s t hst A hA B hB)
  exact avram_p3_b_bvjump_original_P2_intrinsic_fully_constructed_stopped_signed_mean_zero
    X hBV NX hNX hP2 T τ hτBound hτ x D hD w hw_cont hw_neg
    q hq a b L R ha ha2 hab hL hR hLip hWbound E hEm
    hEregion hν G hG H hH
