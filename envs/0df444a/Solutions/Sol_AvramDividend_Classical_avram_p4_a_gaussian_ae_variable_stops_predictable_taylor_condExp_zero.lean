-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_variable_stops_predictable_taylor_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:26:31.998022+00:00
-- url     : https://prove2.me/submissions/d56949e3-00f8-44b9-ac38-c04ae0985de8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Source-specific predictable compensated Gaussian Taylor cells at
different original bounded stopping times, each conditionally centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i ∈ S, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (B : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ B i)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (G i))
    (hH : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
        (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω))) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (((X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
          Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
        (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
          Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)) ^ 2)) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
        Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
      (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
        Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    ∀ i (hi : i ∈ S), Integrable (F i) P ∧
      P[F i | (isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
      Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
    (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
      Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
  let MY : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * M i ω + (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  let FY : ι → Ω → ℝ := fun i ω =>
    G i ω * MY i ω + (H i ω * MY i ω ^ 2 - ((h i : ℝ) * Y.σ ^ 2) * H i ω)
  change ∀ i (hi : i ∈ S), Integrable (F i) P ∧
    P[F i | (isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  intro i hi
  have hME : M i =ᵐ[P] MY i := by
    filter_upwards [hSourceDecomp] with ω hω
    dsimp [M, MY]
    rw [hω (τ i ω + h i), hω (τ i ω)]
    push_cast
    ring
  have hGIY : Integrable (fun ω => G i ω * MY i ω) P := by
    apply (hGI i hi).congr
    filter_upwards [hME] with ω he
    exact congrArg (fun z => G i ω * z) he
  have hH2IY : Integrable (fun ω => H i ω * MY i ω ^ 2) P := by
    apply (hH2I i hi).congr
    filter_upwards [hME] with ω he
    exact congrArg (fun z : ℝ => H i ω * z ^ 2) he
  obtain ⟨hIntY, hCondY⟩ :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_residual_condExp_zero
      Y hYν (τ i) (hτ i hi) (B i) (hbounded i hi) (h i)
      (G i) (H i) (hG i hi) (hH i hi) hGIY (hHI i hi) hH2IY
  have hFAE : F i =ᵐ[P] FY i := by
    filter_upwards [hME] with ω he
    dsimp [F, FY]
    rw [he, hYσ]
  change Integrable (F i) P ∧
    P[F i | (isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  exact ⟨hIntY.congr hFAE.symm,
    (condExp_congr_ae
      (m := (isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace)
      hFAE).trans hCondY⟩
