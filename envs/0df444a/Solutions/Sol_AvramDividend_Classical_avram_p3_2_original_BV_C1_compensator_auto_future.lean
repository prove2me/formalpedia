-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_original_BV_C1_compensator_auto_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:16:50.04447+00:00
-- url     : https://prove2.me/submissions/e79ae9a0-1304-47ab-962b-ba8162670fcc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightcont_source_future_of_P2
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_actual_BV_C1_stopped_jump_compensator_L1_zero_mean_from_local_band

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The literal BV controlled-process C1 local-band jump martingale has
verified original future-rectangle intensity without an extra hypothesis. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ}
  (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
  (NX : Ω → Measure (ℝ≥0 × ℝ))
  (hNX : ∀ ω, NX ω = ((Measure.count.restrict
    {u : ℝ≥0 | 0 < u ∧ X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
    (fun u : ℝ≥0 => (u, X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
  (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
    (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ))
    (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
  (MK : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMK : MK = P.bind K) (T : ℝ≥0)
  (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
  (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
  (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
      (inferInstance : MeasurableSpace ℝ)))
  (hMT : MT = MK.restrict S)
  (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
  (hμfinite : μ Set.univ < ∞)
  (hμclock : ∀ A : Set (ℝ≥0 × Ω),
    MeasurableSet[𝓕.rightCont.predictable] A →
    μ A = ((((volume : Measure ℝ).restrict
      (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
  (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
    𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
  (τ : Ω → ℝ≥0) (hτBound : ∀ ω, τ ω ≤ T)
  (hτ : IsStoppingTime 𝓕.rightCont
    (fun ω => (τ ω : WithTop ℝ≥0)))
  (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
  (q : ℝ) (hq : 0 ≤ q) (a b L R : ℝ)
  (ha : 0 < a) (ha2 : a ≤ 2) (hab : a ≤ b)
  (hL : 0 ≤ L) (hR : 0 ≤ R)
  (hLip : ∀ u ∈ Icc (a / 2) b, ∀ v ∈ Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v|)
  (hWbound : ∀ v : ℝ, v ≤ b → |w v| ≤ R)
  (E : Set (ℝ≥0 × Ω))
  (hEregion : ∀ p ∈ E,
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
  (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
  (hH : H = fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ (τ p.1.2 : ℝ≥0∞) then G p else 0)
  (hSupport : S.indicator H = H) :
  Integrable (fun ω =>
    (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧
  (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
    (∫ t, ∫ z, H ((t, ω), z)
      ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C') =
        N ((Set.Ioi i ×ˢ A) ×ˢ C') := by
    intro i A C' hi hC'
    rw [hMT, hST]
    exact avram_p4_f_assembly_original_rightcont_source_future_of_P2
      X T NX hNX K hK MK hMK μ hμclock N hN i A hi C' hC'
  exact avram_wave8_22_actual_BV_C1_stopped_jump_compensator_L1_zero_mean_from_local_band
    X hBV NX hNX K hK MK hMK T S hST hS MT N hMT
    μ hμfinite hμclock hN hFuture τ hτBound hτ x D w q hq
    a b L R ha ha2 hab hL hR hLip hWbound E hEregion
    hMass G hG hGm H hH hSupport
