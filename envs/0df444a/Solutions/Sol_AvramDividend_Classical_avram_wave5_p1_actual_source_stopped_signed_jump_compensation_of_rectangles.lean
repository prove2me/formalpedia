-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:53:01.064944+00:00
-- url     : https://prove2.me/submissions/ed3d082e-92a7-4dc7-9d29-6df630696681

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

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
        (fun u : ℝ≥0 =>
          (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] G)
    (hGi : Integrable G M)
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : H = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then G p else 0)
    (hActualI : Integrable
      (fun ω => ∫ p, H ((p.1, ω), p.2) ∂(NX ω)) P)
    (hSourceFubini :
      (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) =
        ∫ p, H p ∂M) :
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] H ∧
    Integrable H M ∧ Integrable H N ∧
      (∫ ω, ∫ p, H ((p.1, ω), p.2) ∂(NX ω) ∂P) -
        (∫ p, H p ∂N) = 0 := by
  classical
  subst H
  have htransfer :=
    AvramDividend.Classical.avram_wave4_p1_sigma_stopped_predictable_marked_l1_transfer
      𝓕 M N B hBm hBmono hBcover hLocal hBot hFuture
      τ hτ G hGm hGi
  dsimp at htransfer
  rcases htransfer with ⟨hMeas, hIntM, hIntN, hEq⟩
  refine ⟨hMeas, hIntM, hIntN, ?_⟩
  rw [hSourceFubini, hEq]
  simp
