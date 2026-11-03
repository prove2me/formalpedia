-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_03_original_rightCont_stopped_gaussian_history_weighted_condExp_quadratic_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:57:39.466065+00:00
-- url     : https://prove2.me/submissions/4ff592bb-0ab4-4801-af53-f1bbe72a0ad4

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original stopped Gaussian predictable quadratic term has exact conditional half-bracket drift. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ℝ≥0) (H : Ω → ℝ)
    (hH : Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] H)
    (hProdI : Integrable (fun ω =>
      H ω * (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) P) :
    P[(fun ω => H ω *
      (X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * H ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hτ
  let Y : Ω → ℝ := fun ω =>
    X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c
  have hMom :=
    avram_wave6_03_original_rightCont_stopped_gaussian_condExp_mean_variance
      X hν τ hτ B hbounded h
  change Integrable Y P ∧
    (P[Y | hτstop.measurableSpace] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable (fun ω => Y ω ^ 2) P ∧
    (P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace]
      =ᵐ[P] (fun _ => (h : ℝ) * X.σ ^ 2)) at hMom
  have hHYI : Integrable (H * (fun ω => Y ω ^ 2)) P := hProdI
  have hPull : P[H * (fun ω => Y ω ^ 2) | hτstop.measurableSpace] =ᵐ[P]
      H * P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace] :=
    condExp_mul_of_stronglyMeasurable_left
      hH.stronglyMeasurable hHYI hMom.2.2.1
  change P[H * (fun ω => Y ω ^ 2) | hτstop.measurableSpace]
    =ᵐ[P] (fun ω => ((h : ℝ) * X.σ ^ 2) * H ω)
  filter_upwards [hPull, hMom.2.2.2] with ω hp hz
  calc
    (P[H * (fun ω => Y ω ^ 2) | hτstop.measurableSpace]) ω =
        (H * P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace]) ω := hp
    _ = H ω * (P[(fun ω => Y ω ^ 2) | hτstop.measurableSpace]) ω := rfl
    _ = H ω * ((h : ℝ) * X.σ ^ 2) := by rw [hz]
    _ = ((h : ℝ) * X.σ ^ 2) * H ω := mul_comm _ _
