-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussian12_original_zerojump_masked_gaussian_L1_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T21:48:17.864985+00:00
-- url     : https://prove2.me/submissions/067dd6b8-9712-4332-80c0-1f2ac9f86895

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zero_jump_stopped_gaussian_cells
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_original_zerojump_finite_gaussian_grid_positive_mask
import Theorems.Thm_AvramDividend_Classical_avram_gaussian12_restricted_L1_limit_preserves_zero_mean
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (hA : MeasurableSet {ω : Ω | σ ω ≠ 0})
    (S : ℕ → Finset ι) (τ : ℕ → ι → Ω → ℝ≥0)
    (hτ : ∀ n, ∀ i ∈ S n, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ n i ω ≤ s})
    (B : ℕ → ι → ℝ≥0)
    (hbounded : ∀ n, ∀ i ∈ S n, ∀ ω, τ n i ω ≤ B n i)
    (h : ℕ → ι → ℝ≥0) (G H : ℕ → ι → Ω → ℝ)
    (hG : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i)
        (hτ n i hi)).measurableSpace] (G n i))
    (hH : ∀ n i (hi : i ∈ S n),
      Measurable[(isStoppingTime_withTop_of_le_events (τ n i)
        (hτ n i hi)).measurableSpace] (H n i))
    (M : ℕ → ι → Ω → ℝ)
    (hM : ∀ n, M n = (fun i ω =>
        (X.X (τ n i ω + h n i) ω -
          ((τ n i ω + h n i) : ℝ) * X.c) -
        (X.X (τ n i ω) ω - (τ n i ω : ℝ) * X.c)))
    (hGI : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => G n i ω * M n i ω) P)
    (hHI : ∀ n, ∀ i ∈ S n, Integrable (H n i) P)
    (hH2I : ∀ n, ∀ i ∈ S n,
      Integrable (fun ω => H n i ω * (M n i ω) ^ 2) P)
    (Z : Ω → ℝ) (hZI : Integrable Z P) :
    let F : ℕ → ι → Ω → ℝ := fun n i ω =>
      G n i ω * M n i ω +
        (H n i ω * M n i ω ^ 2 -
          ((h n i : ℝ) * X.σ ^ 2) * H n i ω)
    let Q : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ S n, F n i ω
    Tendsto (fun n => ∫⁻ ω in {ω : Ω | σ ω ≠ 0},
        ‖Q n ω - Z ω‖ₑ ∂P) atTop (nhds (0 : ℝ≥0∞)) →
      (∫ ω in {ω : Ω | σ ω ≠ 0}, Z ω ∂P) = 0 := by
  dsimp only
  intro hL1
  let F : ℕ → ι → Ω → ℝ := fun n i ω =>
    G n i ω * M n i ω +
      (H n i ω * M n i ω ^ 2 -
        ((h n i : ℝ) * X.σ ^ 2) * H n i ω)
  let Q : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ S n, F n i ω
  have hFI : ∀ n, ∀ i ∈ S n, Integrable (F n i) P := by
    intro n i hi
    have hc :=
      AvramDividend.Classical.avram_gaussian12_original_zero_jump_stopped_gaussian_cells
        X hν (S n) (τ n) (hτ n) (B n) (hbounded n)
        (h n) (G n) (H n) (hG n) (hH n) (M n) (hM n)
        (hGI n) (hHI n) (hH2I n)
    exact (hc i hi).1
  have hQI : ∀ n, Integrable (Q n) P := by
    intro n
    exact integrable_finset_sum (S n) (hFI n)
  have hZero : ∀ n,
      (∫ ω in {ω : Ω | σ ω ≠ 0}, Q n ω ∂P) = 0 := by
    intro n
    exact
      AvramDividend.Classical.avram_gaussian12_original_zerojump_finite_gaussian_grid_positive_mask
        X hν σ hσstop (S n) (τ n) (hτ n)
        (B n) (hbounded n) (h n) (G n) (H n)
        (hG n) (hH n) (M n) (hM n)
        (hGI n) (hHI n) (hH2I n)
  exact
    AvramDividend.Classical.avram_gaussian12_restricted_L1_limit_preserves_zero_mean
      {ω : Ω | σ ω ≠ 0} hA Q hQI Z hZI hZero hL1
