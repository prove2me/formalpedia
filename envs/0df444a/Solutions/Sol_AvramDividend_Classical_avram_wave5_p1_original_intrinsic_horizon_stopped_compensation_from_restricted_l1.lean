-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_original_intrinsic_horizon_stopped_compensation_from_restricted_l1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:31:52.930719+00:00
-- url     : https://prove2.me/submissions/278c38ff-df85-4012-84f4-f8f86fddae4e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Original stopped Lévy jump reward has integrable source term and zero expected compensated term. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      MT (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGi : Integrable G MT)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H MT ∧ Integrable H N ∧
    Integrable (fun ω =>
      ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P ∧
    (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
      (∫ p, H p ∂N) = 0 := by
  classical
  subst H
  have htransfer :=
    avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
      𝓕 MT N B hBm hBmono hBcover hLocal hBot hFuture
      τ hτ G hGm hGi
  dsimp at htransfer
  rcases htransfer with ⟨hHm, hHMT, hHN, hEq⟩
  have hHi : Integrable
      (fun p : ((ℝ≥0 × Ω) × ℝ) =>
        if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) M := by
    letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
      @Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)
    have hRestr : Integrable
        (fun p : ((ℝ≥0 × Ω) × ℝ) =>
          if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
        (M.restrict S) := by
      rw [← hMT]
      exact hHMT
    have hIndicator := (integrable_indicator_iff hS).2 hRestr
    simpa only [hSupport] using hIndicator
  have hFibre :=
    avram_wave5_p1_original_intrinsic_jump_fibres_integrable_ae_of_global_l1
      X NX hNX K hK hKmeas M hM _ hHm hHi
  have hActualI :=
    avram_wave5_p1_original_intrinsic_jump_integral_integrable_from_global_l1
      X NX hNX K hK hKmeas M hM _ hHi hHm hFibre
  have hSource :=
    avram_wave5_p1_original_signed_source_fubini_of_integrable_predictable
      X NX hNX K hK hKmeas M hM _ hHi hHm
  have hExpected :
      (∫ ω, ∫ p,
        (if (p.1 : ℝ≥0∞) ≤ τ ω then G ((p.1, ω), p.2) else 0)
          ∂(NX ω) ∂P) =
      ∫ p, (if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) ∂MT := by
    calc
      _ = ∫ p, (if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) ∂M :=
        hSource
      _ = ∫ p, (if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0) ∂MT := by
        rw [hMT, ← integral_indicator hS, hSupport]
  refine ⟨hHm, hHMT, hHN, hActualI, ?_⟩
  rw [hExpected, hEq]
  simp