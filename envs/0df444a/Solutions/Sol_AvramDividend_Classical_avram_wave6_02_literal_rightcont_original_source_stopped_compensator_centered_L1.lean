-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_02_literal_rightcont_original_source_stopped_compensator_centered_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:00:40.575789+00:00
-- url     : https://prove2.me/submissions/8f4c3f85-7a81-40d3-9da5-a1649b23692a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_literal_rightcont_original_source_stopped_l1_compensation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
  :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ)) := fun ω =>
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω)
    ∀     (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont ⊥] A → MeasurableSet C →
      MT (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGiN : Integrable G N)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hSupport : S.indicator H = H),
    Integrable (fun ω =>
      (∫ p, H ((p.1, ω), p.2) ∂(NX ω)) - (∫ p, H p ∂N)) P ∧
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ p, H p ∂N)) ∂P) = 0 := by
  classical
  intro NX K M hM T S hST MT N hMT B hBm hBmono hBcover hLocal hBot
    hFuture τ hτ G hGm hGiN H hH hSupport
  obtain ⟨_, _, _, hJumpI, hMean⟩ :=
    avram_wave5_02c_literal_rightcont_original_source_stopped_l1_compensation
      X M hM T S hST MT N hMT B hBm hBmono hBcover
      hLocal hBot hFuture τ hτ G hGm hGiN H hH hSupport
  have hConst : Integrable (fun _ : Ω => ∫ p, H p ∂N) P := integrable_const _
  refine ⟨hJumpI.sub hConst, ?_⟩
  calc
    (∫ ω, ((∫ p, H ((p.1, ω), p.2) ∂(NX ω)) -
      (∫ p, H p ∂N)) ∂P) =
        (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
        (∫ _ : Ω, (∫ p, H p ∂N) ∂P) := integral_sub hJumpI hConst
    _ = (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
        (∫ p, H p ∂N) := by simp
    _ = 0 := hMean