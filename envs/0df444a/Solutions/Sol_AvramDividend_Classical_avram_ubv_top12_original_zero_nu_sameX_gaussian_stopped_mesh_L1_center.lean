-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_top12_original_zero_nu_sameX_gaussian_stopped_mesh_L1_center
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:25:54.739976+00:00
-- url     : https://prove2.me/submissions/48fe8a95-c615-4b4b-aee3-f75379210720

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_ae_original_predictable_stopped_mesh_L1_limit_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original source is its own Gaussian component when its Lévy jump
    intensity vanishes, so predictable stopped L1 limits retain mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hGstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (G n i))
    (hHstopped : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i) (hτ n i hi)).measurableSpace]
        (H n i))
    (hGglobal : ∀ n, ∀ i ∈ S n, Measurable (G n i))
    (hHglobal : ∀ n, ∀ i ∈ S n, Measurable (H n i))
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : ∀ u ω, Z u ω = X.X u ω - (u : ℝ) * X.c)
    (hGI : ∀ n, ∀ i ∈ S n, Integrable (fun ω => G n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω)) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n, Integrable (fun ω => H n i ω *
      (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2) P)
    (f : Ω → ℝ) (hf : AEStronglyMeasurable f P)
    (F : ℕ → Ω → ℝ)
    (hF : ∀ n ω, F n ω = ∑ i ∈ S n,
        (G n i ω * (Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) +
        (1 / 2 : ℝ) * H n i ω *
          ((Z (τ n i ω + h n i) ω - Z (τ n i ω) ω) ^ 2 -
            (h n i : ℝ) * X.σ ^ 2)))
    (hL1 : Tendsto (fun n => ∫⁻ ω, ‖F n ω - f ω‖ₑ ∂P)
      atTop (nhds 0)) :
    (∫ ω, f ω ∂P) = 0 := by
  have hSource : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (X.X u ω - (u : ℝ) * X.c) + (0 : ℝ) + 0 := by
    filter_upwards [] with ω
    intro u
    ring
  have hZsame : ∀ u ω, Z u ω = X.X u ω - (u : ℝ) * X.c - 0 - 0 := by
    intro u ω
    simpa only [sub_zero] using hZ u ω
  exact avram_p4_a_gaussian_ae_original_predictable_stopped_mesh_L1_limit_mean_zero
    X X hNuZero rfl (fun _ _ => 0) (fun _ _ => 0)
    hSource S τ hτ B hbounded h G H hGstopped hHstopped hGglobal hHglobal
    Z hZsame hGI hHI hH2I f hf F hF hL1
