-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_05_original_stopped_gaussian_finite_bounded_predictable_gain_sum_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:41:33.269175+00:00
-- url     : https://prove2.me/submissions/a2e5e0cc-bf3f-4b09-9547-69770ab8fcc2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕.rightCont s] {ω : Ω | τ ω ≤ s})
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    {ι : Type*} (S : Finset ι)
    (h : ι → ℝ≥0) (G : ι → Ω → ℝ)
    (hGstop : ∀ i ∈ S,
      Measurable[(isStoppingTime_withTop_of_le_events τ hτ).measurableSpace] (G i))
    (hGglobal : ∀ i ∈ S, Measurable (G i))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K i) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)
    (∀ i ∈ S, MemLp (F i) 2 P) ∧
      Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
        (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0 := by
  classical
  let F : ι → Ω → ℝ := fun i ω =>
    G i ω * (X.X (τ ω + h i) ω - X.X (τ ω) ω - (h i : ℝ) * X.c)
  have hPoint :
      ∀ i ∈ S,
        MemLp (F i) 2 P ∧
        Integrable (F i) P ∧
          (∫ ω, F i ω ∂P) = 0 := by
    intro i hi
    have hOne :=
      avram_wave7_05_original_stopped_gaussian_bounded_predictable_gain_L2_mean_zero
        X hν τ hτ T hbounded (h i) (G i)
          (hGstop i hi) (hGglobal i hi) (K i)
          (hK i hi) (hGbound i hi)
    dsimp only at hOne
    simpa only [F] using hOne
  have hLpAll : ∀ i ∈ S, MemLp (F i) 2 P := by
    intro i hi
    exact (hPoint i hi).1
  have hIntAll : ∀ i ∈ S, Integrable (F i) P := by
    intro i hi
    exact (hPoint i hi).2.1
  have hSumI : Integrable (fun ω => ∑ i ∈ S, F i ω) P :=
    integrable_finset_sum S hIntAll
  change (∀ i ∈ S, MemLp (F i) 2 P) ∧
    Integrable (fun ω => ∑ i ∈ S, F i ω) P ∧
      (∫ ω, ∑ i ∈ S, F i ω ∂P) = 0
  refine ⟨hLpAll, hSumI, ?_⟩
  calc
    (∫ ω, ∑ i ∈ S, F i ω ∂P) =
      ∑ i ∈ S, ∫ ω, F i ω ∂P :=
      integral_finset_sum S hIntAll
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact (hPoint i hi).2.2
