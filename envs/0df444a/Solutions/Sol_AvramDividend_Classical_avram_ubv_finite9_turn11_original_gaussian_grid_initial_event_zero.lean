-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_turn11_original_gaussian_grid_initial_event_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:38:34.798272+00:00
-- url     : https://prove2.me/submissions/f969c2d1-4361-44ec-9fd0-ef63095e2478

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_stopped_condexp_initial_event_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual stopped Gaussian Taylor cell sums are centred on every event
observable in the original initial filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (G i))
    (hH : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i)
        (hτ i hi)).measurableSpace] (H i))
    (M : ι → Ω → ℝ)
    (hM : M = (fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c)))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω * M i ω) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S,
      Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    (∫ ω in A, ∑ i ∈ S, F i ω ∂P) = 0 := by
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * M i ω +
      (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  change (∫ ω in A, ∑ i ∈ S, F i ω ∂P) = 0
  have hCells :=
    AvramDividend.Classical.avram_gaussian12_original_zero_jump_stopped_gaussian_cells
      X hν S τ hτ B hbounded h G H hG hH M hM hGI hHI hH2I
  have hStop : ∀ i ∈ S, IsStoppingTime 𝓕.rightCont
      (fun ω => (τ i ω : WithTop ℝ≥0)) := by
    intro i hi
    exact isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)
  rw [integral_finset_sum S (by
    intro i hi
    exact ((hCells i hi).1).integrableOn)]
  apply Finset.sum_eq_zero
  intro i hi
  exact
    AvramDividend.Classical.avram_ubv_finite9_turn11_stopped_condexp_initial_event_zero
      (τ i) (hStop i hi) (F i) (hCells i hi).1
      (hCells i hi).2 A hA
