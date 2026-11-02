-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_actual_physical_clock_general_stopped_source_L1_compensation_finite_levy_bands
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:40:59.99899+00:00
-- url     : https://prove2.me/submissions/3371ef26-5d28-4b65-88e8-c06ca11865a5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_physical_clock_general_stopped_source_L1_compensation_no_hBot
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine physical clock and finite Lévy bands supply all local source compensation finiteness. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ)) (hNX : ∀ ω, NX ω = ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧ X.X u ω -
    Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
    (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))) (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
    (inferInstance : MeasurableSpace (ℝ≥0 × ℝ)) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)) (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P) (M : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K) (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ)) (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S) (MT N : @Measure ((ℝ≥0 × Ω) × ℝ) (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
    (inferInstance : MeasurableSpace ℝ))) (hMT : MT = M.restrict S) (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)) (hμfinite : μ Set.univ < ∞)
    (hμclock : ∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A → μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hBfinite : ∀ k, (X.ν.restrict (Iio (0 : ℝ))) (B k) < ∞) (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ), MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' → MT ((Set.Ioi i ×ˢ A) ×ˢ C') =
    N ((Set.Ioi i ×ˢ A) ×ˢ C')) (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ) (G : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hGm : Measurable[(@Prod.instMeasurableSpace _ _
    (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G) (hGiN : Integrable G N) (H : ((ℝ≥0 × Ω) × ℝ) → ℝ) (hH : H = fun p =>
    if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) (hSupport : S.indicator H = H) : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H MT ∧ Integrable H N ∧ Integrable (fun ω => ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P ∧ (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
    (∫ p, H p ∂N) = 0 := by
  classical
  have hKsource : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) := by
    intro ω
    rw [hK ω, hNX ω]
  have hLocal : ∀ k,
      MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞ := by
    intro k
    exact
      avram_wave5_03_actual_true_clock_initial_future_rectangles_force_finite_mark_band
        X K hKsource M hM T S MT N hMT μ hμfinite hμclock hN
        (B k) (hBm k) (hBfinite k) hFuture
  exact avram_wave5_03_actual_physical_clock_general_stopped_source_L1_compensation_no_hBot
    X NX hNX K hK hKmeas M hM T S hST hS MT N hMT
    μ hμclock hN B hBm hBmono hBcover hLocal hFuture
    τ hτ G hGm hGiN H hH hSupport
