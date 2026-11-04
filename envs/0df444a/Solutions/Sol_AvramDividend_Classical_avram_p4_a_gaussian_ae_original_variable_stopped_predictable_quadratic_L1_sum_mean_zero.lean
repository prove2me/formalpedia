-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_ae_original_variable_stopped_predictable_quadratic_L1_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:30:48.722548+00:00
-- url     : https://prove2.me/submissions/c4d2db25-8728-497d-8aeb-11c38796b74f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite collection of genuine original-source stopped Gaussian quadratic
tests has zero expected compensated square, with variable clocks and L1 gains. -/
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
    (h : ι → ℝ≥0) (H : ι → Ω → ℝ)
    (hHstopped : ∀ i (hi : i ∈ S),
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i hi)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, Measurable (H i))
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
    Integrable (fun ω => ∑ i ∈ S,
      H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) P ∧
      (∫ ω, ∑ i ∈ S,
        H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2) ∂P) = 0 := by
  let M : ι → Ω → ℝ := fun i ω =>
    (X.X (τ i ω + h i) ω - ((τ i ω + h i) : ℝ) * X.c -
      Jsmall (τ i ω + h i) ω - Jlarge (τ i ω + h i) ω) -
    (X.X (τ i ω) ω - (τ i ω : ℝ) * X.c -
      Jsmall (τ i ω) ω - Jlarge (τ i ω) ω)
  let MY : ι → Ω → ℝ := fun i ω =>
    Y.X (τ i ω + h i) ω - Y.X (τ i ω) ω - (h i : ℝ) * Y.c
  have hAE (i : ι) : M i =ᵐ[P] MY i := by
    filter_upwards [hSourceDecomp] with ω hw
    dsimp [M, MY]
    rw [hw (τ i ω + h i), hw (τ i ω)]
    push_cast
    ring
  have hQI : ∀ i ∈ S, Integrable (fun ω =>
      H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) P ∧
      (∫ ω, H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2) ∂P) = 0 := by
    intro i hi
    have hY2I : Integrable (fun ω => H i ω * (MY i ω) ^ 2) P :=
      (hH2I i hi).congr (by
        filter_upwards [hAE i] with ω hm
        change H i ω * M i ω ^ 2 = H i ω * MY i ω ^ 2
        rw [hm])
    have hYQ :=
      avram_wave6_03_original_rightCont_stopped_gaussian_compensated_square_test_zero
        Y hYν (τ i) (hτ i hi) (B i) (hbounded i hi) (h i)
        (H i) (hHstopped i hi) (hHglobal i hi) (hHI i hi) hY2I
    have hQAE : (fun ω => H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) =ᵐ[P]
        (fun ω => H i ω * (MY i ω ^ 2 - (h i : ℝ) * Y.σ ^ 2)) := by
      filter_upwards [hAE i] with ω hm
      simp only [hm, hYσ]
    exact ⟨hYQ.1.congr hQAE.symm, (integral_congr_ae hQAE).trans hYQ.2⟩
  change Integrable (fun ω => ∑ i ∈ S,
    H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2)) P ∧
    (∫ ω, ∑ i ∈ S,
      H i ω * (M i ω ^ 2 - (h i : ℝ) * X.σ ^ 2) ∂P) = 0
  constructor
  · exact integrable_finset_sum S (fun i hi => (hQI i hi).1)
  · rw [integral_finset_sum S (fun i hi => (hQI i hi).1)]
    exact Finset.sum_eq_zero (fun i hi => (hQI i hi).2)
