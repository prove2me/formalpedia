-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a218_gaussian_chernoff_uniform_finite_mesh_integral_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:49:22.105443+00:00
-- url     : https://prove2.me/submissions/3a3955cb-632b-4899-87bd-2e42211042cf

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : ℕ → ℕ → Ω → ℝ) (b c : ℝ) (hc : 0 < c)
    (hInt : ∀ m i, i < m → Integrable (f m i) P)
    (hPos : ∀ m i ω, 0 ≤ f m i ω)
    (hCell : ∀ m i, i < m →
      (∫ ω, f m i ω ∂P) ≤
        Real.exp (b - c * ((m : ℝ) + 1))) :
    Tendsto (fun m : ℕ =>
      ∫ ω, (∑ i ∈ Finset.range m, f m i ω) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  have hLow (m : ℕ) : 0 ≤
      (∫ ω, (∑ i ∈ Finset.range m, f m i ω) ∂P) := by
    apply integral_nonneg
    intro ω
    apply Finset.sum_nonneg
    intro i hi
    exact hPos m i ω
  have hHigh (m : ℕ) :
      (∫ ω, (∑ i ∈ Finset.range m, f m i ω) ∂P) ≤
        ((m : ℝ) + 1) * Real.exp (b - c * ((m : ℝ) + 1)) := by
    calc
      (∫ ω, (∑ i ∈ Finset.range m, f m i ω) ∂P) =
          ∑ i ∈ Finset.range m, ∫ ω, f m i ω ∂P := by
            rw [integral_finset_sum (Finset.range m) (by
              intro i hi
              exact hInt m i (Finset.mem_range.mp hi))]
      _ ≤ ∑ i ∈ Finset.range m,
          Real.exp (b - c * ((m : ℝ) + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hCell m i (Finset.mem_range.mp hi)
      _ = (m : ℝ) * Real.exp (b - c * ((m : ℝ) + 1)) := by simp
      _ ≤ ((m : ℝ) + 1) * Real.exp (b - c * ((m : ℝ) + 1)) := by
        nlinarith [Real.exp_pos (b - c * ((m : ℝ) + 1))]
  exact squeeze_zero hLow hHigh
    (avram_ga_a70_gaussian_physical_mesh_exponential_tail_weighted_cellcount_vanish b c hc)
