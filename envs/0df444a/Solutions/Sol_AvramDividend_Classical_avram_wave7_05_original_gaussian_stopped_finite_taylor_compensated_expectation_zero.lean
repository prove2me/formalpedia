-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_gaussian_stopped_finite_taylor_compensated_expectation_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T11:53:53.638094+00:00
-- url     : https://prove2.me/submissions/dacdce7c-625c-4d90-bb46-18b3c6be2d5c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hH : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω =>
      G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω =>
      H i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c) ^ 2) P) :
    let Y : ι → Ω → ℝ := fun i ω =>
      X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * Y i ω +
        (H i ω * Y i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp only
  let Y : ι → Ω → ℝ := fun i ω =>
    X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * Y i ω +
      (H i ω * Y i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  have hCell :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
      X hν S τ hτ B hbounded h G H hG hH hGI hHI hH2I
  dsimp only at hCell
  have hInt : Integrable (fun ω => ∑ i ∈ S, F i ω) P := hCell.1
  have hCE :
      P[(fun ω => ∑ i ∈ S, F i ω) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := hCell.2
  have hIntegralEq :
      (∫ ω, (P[(fun ω => ∑ i ∈ S, F i ω) |
        (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P) =
        ∫ ω, ∑ i ∈ S, F i ω ∂P :=
    integral_condExp (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace_le
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0
  refine ⟨hInt, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
        ∫ ω, (P[(fun ω => ∑ i ∈ S, F i ω) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]) ω ∂P :=
      hIntegralEq.symm
    _ = ∫ ω, (0 : ℝ) ∂P := integral_congr_ae hCE
    _ = 0 := by simp
