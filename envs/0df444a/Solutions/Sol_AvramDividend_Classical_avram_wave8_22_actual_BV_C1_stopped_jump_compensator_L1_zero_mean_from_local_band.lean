-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_actual_BV_C1_stopped_jump_compensator_L1_zero_mean_from_local_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:46:17.82553+00:00
-- url     : https://prove2.me/submissions/5320ab14-a502-4ddf-827e-d216b5c3d44f

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_stopped_signed_jump_minus_true_predictable_compensator_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_rightcont_predictable_kernel_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

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
  (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
    MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
    MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C'))
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
  have hKmeas : AEMeasurable K P := by
    apply avram_wave5_02a_original_rightcont_predictable_kernel_measurable X K
    intro ω
    rw [hK ω, hNX ω]
  rcases avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands X
    with ⟨bands, hBm, hBfinite, hBmono, hBcover⟩
  have hGstrong : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      AEStronglyMeasurable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by
    exact hGm.aestronglyMeasurable
  have hGproduct : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      Integrable G (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) :=
    avram_wave7_02_original_BV_C1_actual_controlled_predictable_full_negative_jump_kernel_product_L1
      X hBV x D w q hq a b L R ha ha2 hab hL hR
      hLip hWbound μ hμfinite E hEregion hMass G hG hGstrong
  have hGiN : Integrable G N := by
    rw [hN]
    exact hGproduct
  exact avram_wave8_22_original_stopped_signed_jump_minus_true_predictable_compensator_L1_zero_mean
    X NX hNX K hK hKmeas MK hMK T S hST hS MT N hMT
    μ hμfinite hμclock hN bands hBm hBmono hBcover hBfinite
    hFuture (fun ω => (τ ω : ℝ≥0∞)) hτ G hGm hGiN H hH hSupport
