-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_full_sum_L2_small_time_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:04:01.034204+00:00
-- url     : https://prove2.me/submissions/27ea2625-4c94-4e0c-aaee-6e8003c16d9c

import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero

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
      (∫ ω, (∑ i ∈ S,
        H i ω * (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
          (h : ℝ) * X.c)) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
  classical
  let Q : ι → ℝ≥0 → Ω → ℝ := fun i h ω =>
    H i ω * (X.X (τ i ω + h) ω - X.X (τ i ω) ω -
      (h : ℝ) * X.c)
  change Filter.Tendsto
    (fun h : ℝ≥0 => ∫ ω, (∑ i ∈ S, Q i h ω) ^ 2 ∂P)
    (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ))
  have hMem (h : ℝ≥0) : MemLp (fun ω => ∑ i ∈ S, Q i h ω) 2 P := by
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_sum_MemLp_two
      X hν S τ hτ T hbounded (fun _ => h) H hH K hK hBound
  have hCellMem (i : ι) (h : ℝ≥0) : MemLp (Q i h) 2 P := by
    exact avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_weighted_true_increment_MemLp_two
      X hν (τ i) (hτ i) (T i) (hbounded i) h
      (H i) (hH i) (K i) (hK i) (hBound i)
  have hInt1 (h : ℝ≥0) :
      Integrable (fun ω => (∑ i ∈ S, Q i h ω) ^ 2) P :=
    (memLp_two_iff_integrable_sq (hMem h).aestronglyMeasurable).mp (hMem h)
  have hInt2 (h : ℝ≥0) :
      Integrable (fun ω => ∑ i ∈ S, (Q i h ω) ^ 2) P := by
    apply integrable_finset_sum S
    intro i hi
    exact (memLp_two_iff_integrable_sq
      (hCellMem i h).aestronglyMeasurable).mp (hCellMem i h)
  have hLo (h : ℝ≥0) :
      0 ≤ (∫ ω, (∑ i ∈ S, Q i h ω) ^ 2 ∂P) :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hHi (h : ℝ≥0) :
      (∫ ω, (∑ i ∈ S, Q i h ω) ^ 2 ∂P) ≤
        (S.card : ℝ) * (∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P) := by
    calc
      (∫ ω, (∑ i ∈ S, Q i h ω) ^ 2 ∂P) ≤
          (∫ ω, (S.card : ℝ) * ∑ i ∈ S, (Q i h ω) ^ 2 ∂P) := by
        apply integral_mono (hInt1 h) ((hInt2 h).const_mul _)
        intro ω
        exact sq_sum_le_card_mul_sum_sq
      _ = (S.card : ℝ) * (∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P) := by
        rw [integral_const_mul]
  have hEnergy : Filter.Tendsto
      (fun h : ℝ≥0 => ∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P)
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    have ht :=
      avram_wave5_03a_actual_rightCont_stopped_gaussian_bounded_grid_square_energy_small_time_zero
        X hν S τ hτ T hbounded H hH K hK hBound
    change Filter.Tendsto
      (fun h : ℝ≥0 => ∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P)
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) at ht
    exact ht
  have hScale : Filter.Tendsto
      (fun h : ℝ≥0 => (S.card : ℝ) *
        (∫ ω, ∑ i ∈ S, (Q i h ω) ^ 2 ∂P))
      (𝓝 (0 : ℝ≥0)) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hEnergy)
  exact squeeze_zero hLo hHi hScale