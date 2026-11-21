-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_bounded_stopped_gaussian_physical_grid_F0_centred
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:46:21.67985+00:00
-- url     : https://prove2.me/submissions/44b9a124-8031-4208-b3fb-ce10ca40f44e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_gaussian_bounded_cell_linear_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_cells_F0_centred
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original finite stopped Gaussian Taylor gains are integrable and initially conditionally centred from predictable bounded coefficients and true second moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hBound : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
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
    (hMI : ∀ i ∈ S, Integrable (M i) P)
    (hM2 : ∀ i ∈ S, Integrable (fun ω => (M i ω) ^ 2) P)
    (hGAE : ∀ i ∈ S, AEStronglyMeasurable (G i) P)
    (hHAE : ∀ i ∈ S, AEStronglyMeasurable (H i) P)
    (BG BH : ι → ℝ)
    (hGB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖G i ω‖ ≤ BG i)
    (hHB : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ BH i) :
    let Q : Ω → ℝ := fun ω =>
      ∑ i ∈ S, (G i ω * M i ω +
        (H i ω * M i ω ^ 2 -
          ((h i : ℝ) * X.σ ^ 2) * H i ω))
    Integrable Q P ∧
    condExp (𝓕.rightCont 0) P Q =ᵐ[P]
      (fun _ => (0 : ℝ))  := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨hGI, hHI, hH2I⟩ :=
    avram_a20_original_gaussian_bounded_cell_linear_square_integrable
      S M G H BG BH hMI hM2 hGAE hHAE hGB hHB
  exact avram_ubv_gauss13_stop_original_cells_F0_centred
    X hν S τ hτ B hBound h G H
    hG hH M hM hGI hHI hH2I
