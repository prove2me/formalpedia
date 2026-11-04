-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_stopped_taylor_finite_condExp_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:26:27.007315+00:00
-- url     : https://prove2.me/submissions/26f07078-840b-4c90-92b7-5c08e6d51c08

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Finite predictable stopped Gaussian Itô–Taylor residuals of actual X
have integrable sum and zero original stopped conditional expectation,
conditional on a same-space all-times Lévy–Itô source extraction. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X Y : SpectrallyNegativeLevy P 𝓕)
    (hYν : Y.ν = 0) (hYσ : Y.σ = X.σ)
    (Jsmall Jlarge : ℝ≥0 → Ω → ℝ)
    (hSourceDecomp : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      X.X u ω = (u : ℝ) * X.c +
        (Y.X u ω - (u : ℝ) * Y.c) + Jsmall u ω + Jlarge u ω)
    (S : Finset ι) (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (B : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ B)
    (h : ι → ℝ≥0) (G H : ι → Ω → ℝ)
    (hG : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hH : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (H i))
    (hGI : ∀ i ∈ S, Integrable (fun ω => G i ω *
      ((X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
        Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
       (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω))) P)
    (hHI : ∀ i ∈ S, Integrable (H i) P)
    (hH2I : ∀ i ∈ S, Integrable (fun ω => H i ω *
      (((X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
          Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
         (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
          Jsmall (τ ω) ω - Jlarge (τ ω) ω)) ^ 2)) P) :
    let M : ι → Ω → ℝ := fun i ω =>
      (X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
        Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
      (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
        Jsmall (τ ω) ω - Jlarge (τ ω) ω)
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * M i ω +
        (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      P[(fun ω => ∑ i ∈ S, F i ω) |
          (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
        =ᵐ[P] (fun _ => (0 : ℝ)) := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (τ ω + h i) ω - ((τ ω + h i) : ℝ) * X.c -
      Jsmall (τ ω + h i) ω - Jlarge (τ ω + h i) ω) -
    (X.X (τ ω) ω - (τ ω : ℝ) * X.c -
      Jsmall (τ ω) ω - Jlarge (τ ω) ω)
  let MY : ι → Ω → ℝ := fun i ω =>
    Y.X (τ ω + h i) ω - Y.X (τ ω) ω - (h i : ℝ) * Y.c
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * M i ω + (H i ω * M i ω ^ 2 - ((h i : ℝ) * X.σ ^ 2) * H i ω)
  let FY : ι → Ω → ℝ := fun i ω =>
    G i ω * MY i ω + (H i ω * MY i ω ^ 2 - ((h i : ℝ) * Y.σ ^ 2) * H i ω)
  have hME (i : ι) : M i =ᵐ[P] MY i := by
    filter_upwards [hSourceDecomp] with ω hω
    dsimp [M, MY]
    rw [hω (τ ω + h i), hω (τ ω)]
    push_cast
    ring
  have hGIY : ∀ i ∈ S, Integrable (fun ω => G i ω * MY i ω) P := by
    intro i hi
    apply (hGI i hi).congr
    filter_upwards [hME i] with ω he
    exact congrArg (fun z => G i ω * z) he
  have hH2IY : ∀ i ∈ S, Integrable (fun ω => H i ω * MY i ω ^ 2) P := by
    intro i hi
    apply (hH2I i hi).congr
    filter_upwards [hME i] with ω he
    exact congrArg (fun z : ℝ => H i ω * z ^ 2) he
  obtain ⟨hIntY, hCondY⟩ :=
    avram_wave6_03_original_rightCont_stopped_gaussian_predictable_taylor_finite_sum_condExp_zero
      Y hYν S τ hτ B hbounded h G H hG hH hGIY hHI hH2IY
  have hSumAE : (fun ω => ∑ i ∈ S, F i ω) =ᵐ[P]
      (fun ω => ∑ i ∈ S, FY i ω) := by
    filter_upwards [hSourceDecomp] with ω hω
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [F, FY, M, MY]
    rw [hω (τ ω + h i), hω (τ ω), hYσ]
    push_cast
    ring
  change Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
    P[(fun ω => ∑ i ∈ S, F i ω) |
      (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace]
      =ᵐ[P] (fun _ => (0 : ℝ))
  exact ⟨hIntY.congr hSumAE.symm,
    (condExp_congr_ae
      (m := (isStoppingTime_withTop_of_le_events τ hτ).measurableSpace)
      hSumAE).trans hCondY⟩
