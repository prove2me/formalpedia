-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_sigma_finite_predictable_marked_campbell_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:43:08.933726+00:00
-- url     : https://prove2.me/submissions/41302517-258e-4ce3-86e0-497c4637e6ab

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_sigma_finite_marked_predictable_measure_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal

/-- Full nonnegative and signed integrable predictable marked-kernel transfer,
derived only from elementary adapted rectangle count-compensation hypotheses. -/
theorem solution
    {Ω E ι : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    (M N : @Measure ((ι × Ω) × E)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE))
    (B : ℕ → Set E) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, M ((Set.univ : Set (ι × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ι)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ι)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ι) (A : Set Ω) (C : Set E),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (G : ((ι × Ω) × E) → ℝ≥0∞)
    (hGm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] G)
    (F : ((ι × Ω) × E) → ℝ)
    (hFm : Measurable[(@Prod.instMeasurableSpace _ _ (𝓕.predictable) mE)] F)
    (hFi : Integrable F M) :
    (∫⁻ p, G p ∂M) = (∫⁻ p, G p ∂N) ∧
      (Integrable F N ∧ (∫ p, F p ∂M) = ∫ p, F p ∂N) := by
  have hMN : M = N :=
    AvramDividend.Classical.avram_wave4_p1_sigma_finite_marked_predictable_measure_unique
      𝓕 M N B hBm hBmono hBcover hLocal hBot hFuture
  subst N
  exact ⟨rfl, hFi, rfl⟩
