-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_bilinear_compensated_bracket_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:48:13.009259+00:00
-- url     : https://prove2.me/submissions/d67f1b84-613e-4278-9344-ea8131d522ce

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (G H : Ω → ℝ)
    (hGstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] G)
    (hHstop : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hGHInt : Integrable (fun ω => G ω * H ω) P)
    (hProductInt : Integrable (fun ω =>
      (G ω * H ω) *
        (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    let Y : Ω → ℝ := fun ω =>
      X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
    P[(fun ω => (G ω * Y ω) * (H ω * Y ω) -
      ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by
  dsimp only
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hBase :
      P[(fun ω => (G ω * H ω) * Y ω ^ 2 -
        ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
    exact avram_wave6_03_original_rightCont_stopped_gaussian_predictable_compensated_quadratic_condExp_zero
      X hν τ hτ B hbounded h (fun ω => G ω * H ω)
        (hGstop.mul hHstop) hGHInt hProductInt
  have hCell :
      (fun ω => (G ω * Y ω) * (H ω * Y ω) -
        ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) =
      (fun ω => (G ω * H ω) * Y ω ^ 2 -
        ((h : ℝ) * X.σ ^ 2) * (G ω * H ω)) := by
    funext ω
    ring
  rw [hCell]
  exact hBase
