-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_stop_original_cells_F0_centred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:30:45.658868+00:00
-- url     : https://prove2.me/submissions/2d6e8d2b-0d15-486a-99fc-77916dc3b049

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_original_gaussian_grid_initial_event_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_initial_event_zero_to_condexp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal
noncomputable section

/-- True original Gaussian stopped cells form an integrable sum centred at F0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
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
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω * (M i ω) ^ 2) P) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
      (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      P[(fun ω => ∑ i ∈ S, F i ω) | 𝓕.rightCont 0] =ᵐ[P]
        (fun _ => (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * M i ω +
    (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    P[(fun ω => ∑ i ∈ S, F i ω) | 𝓕.rightCont 0] =ᵐ[P]
      (fun _ => (0 : ℝ))
  have hCells := avram_gaussian12_original_zero_jump_stopped_gaussian_cells
    X hν S τ hτ B hbounded h G H hG hH M hM hGI hHI hH2I
  have hQ : Integrable (fun ω => ∑ i ∈ S, F i ω) P := by
    exact integrable_finset_sum S (fun i hi => (hCells i hi).1)
  refine ⟨hQ, ?_⟩
  apply avram_ubv_finite9_turn11_initial_event_zero_to_condexp_zero
    (fun ω => ∑ i ∈ S, F i ω) hQ
  intro A hA
  exact avram_ubv_finite9_turn11_original_gaussian_grid_initial_event_zero
    X hν A hA S τ hτ B hbounded h G H hG hH M hM hGI hHI hH2I
