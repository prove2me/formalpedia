-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave8_22_original_stopped_signed_compensator_L1_zero_mean_canonical_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:43:54.189454+00:00
-- url     : https://prove2.me/submissions/6ed53db6-f801-4593-a6d2-a366da8c6d26

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_stopped_signed_jump_minus_true_predictable_compensator_L1_zero_mean
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original stopped centred jump minus its random compensator, with Lévy bands constructed automatically. -/
theorem solution
  {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
  (NX : Ω → Measure (ℝ≥0 × ℝ)) (hNX : ∀ ω, NX ω = ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
  Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
  (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
  (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ) (inferInstance : MeasurableSpace (ℝ≥0 × ℝ)) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
  (inferInstance : MeasurableSpace ℝ)) (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)) (hKmeas : AEMeasurable K P)
  (M : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
  (hM : M = P.bind K) (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T}) (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
  (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S) (MT N : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
  (inferInstance : MeasurableSpace ℝ))) (hMT : MT = M.restrict S) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
  (hμfinite : μ Set.univ < ∞) (hμclock : ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A →
  μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
  𝓕.rightCont.predictable; μ.prod (X.ν.restrict (Iio (0 : ℝ))))) (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ), MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
  MT ((Set.Ioi i ×ˢ A) ×ˢ C') = N ((Set.Ioi i ×ˢ A) ×ˢ C')) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
  (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hGm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
  (hGiN : Integrable G N) (H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hH : H = fun p =>
  if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) (hSupport : S.indicator H = H) : Integrable (fun ω =>
  (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
  ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal))) P ∧ (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
  (∫ t, ∫ z, H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))) ∂(((volume : Measure ℝ).restrict
  (Icc 0 (T : ℝ))).map Real.toNNReal))) ∂P) = 0 := by
  classical
  obtain ⟨B, hBm, hBfinite, hBmono, hBcover⟩ :=
    avram_wave6_02_actual_levy_negative_quadratic_canonical_finite_mark_bands X
  exact avram_wave8_22_original_stopped_signed_jump_minus_true_predictable_compensator_L1_zero_mean
    X NX hNX K hK hKmeas M hM T S hST hS MT N hMT
    μ hμfinite hμclock hN B hBm hBmono hBcover hBfinite
    hFuture τ hτ G hGm hGiN H hH hSupport