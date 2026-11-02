-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_history_finite_grid_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:01:32.863284+00:00
-- url     : https://prove2.me/submissions/c22d553e-c38d-41cf-b048-84446df3f60c

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.NormNum
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
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
    (∫ ω, ∑ i ∈ S, H i ω *
      (X.X (τ i ω + h i) ω - X.X (τ i ω) ω - (h i : ℝ) * X.c) ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hInt (i : ι) (hi : i ∈ S) :
      Integrable (fun ω =>
        H i ω * (X.X (τ i ω + h i) ω - X.X (τ i ω) ω -
          (h i : ℝ) * X.c)) P := by
    have hStop :
        IsStoppingTime 𝓕.rightCont
          (fun ω => (τ i ω : WithTop ℝ≥0)) :=
      isStoppingTime_withTop_of_le_events (τ i) (hτ i)
    exact (avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (τ i) hStop (T i) (hbounded i hi) (h i)
      (H i) (hHglobal i hi) (K i) (hK i hi) (hHbound i hi)).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  rw [integral_finset_sum S (fun i hi => hInt i hi)]
  apply Finset.sum_eq_zero
  intro i hi
  exact avram_wave5_03a_actual_rightCont_stopped_gaussian_history_weighted_mean_zero
    X hν (τ i) (hτ i) (T i) (hbounded i hi) (h i) (H i)
    (hHstopped i) (hHglobal i hi).measurable
