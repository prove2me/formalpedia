-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:46:40.127772+00:00
-- url     : https://prove2.me/submissions/d62925c4-c4dd-4bea-b96f-0b6846752c76

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Order.Filter.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (S : Finset ι)
    (τ : ι → Ω → ℝ≥0)
    (hτ : ∀ i, IsStoppingTime 𝓕.rightCont (fun ω => (τ i ω : WithTop ℝ≥0)))
    (T : ι → ℝ≥0) (hbounded : ∀ i ω, τ i ω ≤ T i)
    (H : ι → Ω → ℝ) (hH : ∀ i, StronglyMeasurable (H i))
    (K : ι → ℝ) (hK : ∀ i, 0 ≤ K i)
    (hBound : ∀ i ω, |H i ω| ≤ K i) :
    Filter.Tendsto (fun h : ℝ≥0 =>
      (∫ ω, ∑ i ∈ S,
        (H i ω * (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
          (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  classical
  let Q : ι → ℝ≥0 → Ω → ℝ := fun i h ω =>
    H i ω * (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
      (h : ℝ) * X.c)
  change Filter.Tendsto
    (fun h : ℝ≥0 => ∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P)
    (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ))
  have hMem (i : ι) (h : ℝ≥0) : MemLp (Q i h) 2 P := by
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (τ i) (hτ i) (T i) (hbounded i) h
      (H i) (hH i) (K i) (hK i) (hBound i)
  have hInt (i : ι) (h : ℝ≥0) :
      Integrable (fun ω => (Q i h ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq (hMem i h).aestronglyMeasurable).mp (hMem i h)
  have hCell (i : ι) :
      Filter.Tendsto (fun h : ℝ≥0 => ∫ ω, (Q i h ω) ^ 2 ∂P)
        (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa only [Q] using
      avram_wave5_03a_actual_rightCont_stopped_gaussian_weighted_true_increment_L2_small_time_zero
        X hν (τ i) (hτ i) (T i) (hbounded i)
        (H i) (hH i) (K i) (hK i) (hBound i)
  have hId (h : ℝ≥0) :
      (∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P) =
        ∑ i ∈ S, ∫ ω, (Q i h ω) ^ 2 ∂P := by
    exact integral_finset_sum S (fun i hi => hInt i h)
  have hSum : Filter.Tendsto
      (fun h : ℝ≥0 => ∑ i ∈ S, ∫ ω, (Q i h ω) ^ 2 ∂P)
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    have ht := tendsto_finset_sum S (fun i hi => hCell i)
    simpa only [Finset.sum_const_zero] using ht
  apply hSum.congr'
  filter_upwards [] with h
  exact (hId h).symm
