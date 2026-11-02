-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_L2_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:06:23.151171+00:00
-- url     : https://prove2.me/submissions/a2edd602-d9a0-4f1f-aa91-fcf47841e294

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i : ι, ∀ s : ℝ≥0,
      MeasurableSet[𝓕.rightCont s] {ω : Ω | τ i ω ≤ s})
    (T : ι → ℝ≥0) (hbounded : ∀ i ∈ S, ∀ ω, τ i ω ≤ T i)
    (h : ι → ℝ≥0)
    (H : ι → Ω → ℝ)
    (hHstopped : ∀ i : ι,
      Measurable[(isStoppingTime_withTop_of_le_events (τ i) (hτ i)).measurableSpace] (H i))
    (hHglobal : ∀ i ∈ S, StronglyMeasurable (H i))
    (K : ι → ℝ) (hK : ∀ i ∈ S, 0 ≤ K i)
    (hHbound : ∀ i ∈ S, ∀ ω, |H i ω| ≤ K i) :
    MemLp (fun ω => ∑ i ∈ S, H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c)) 2 P ∧
    (∫ ω, ∑ i ∈ S, H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by
  classical
  constructor
  · apply memLp_finset_sum S
    intro i hi
    have hStop :
        IsStoppingTime 𝓕.rightCont
          (fun ω => (τ i ω : WithTop ℝ≥0)) :=
      isStoppingTime_withTop_of_le_events (τ i) (hτ i)
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (τ i) hStop (T i) (hbounded i hi) (h i)
      (H i) (hHglobal i hi) (K i) (hK i hi) (hHbound i hi)
  · exact avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
      X hν S τ hτ T hbounded h H hHstopped hHglobal K hK hHbound
