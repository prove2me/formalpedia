-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04b_closed_horizon_real_stieltjes_partition_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:10:34.266865+00:00
-- url     : https://prove2.me/submissions/bda889b4-563d-41f3-92f2-b7d53afafa30

import Mathlib.Data.ENNReal.BigOperators
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A finite genuine closed-horizon Stieltjes integral splits exactly into its time-zero atom and all chronological cells after conversion to reals. -/
theorem solution
    (μ : Measure ℝ) (f : ℝ → ℝ≥0∞)
    (u : ℕ → ℝ) (hu : Monotone u) (hu0 : u 0 = 0) (n : ℕ)
    (hFinite : (∫⁻ s in Icc (0 : ℝ) (u n), f s ∂μ) ≠ ⊤) :
    (∫⁻ s in Icc (0 : ℝ) (u n), f s ∂μ).toReal =
      (∫⁻ s in ({0} : Set ℝ), f s ∂μ).toReal +
      ∑ i ∈ Finset.range n,
        (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ).toReal := by
  have hPartition := avram_wave5_04b_closed_horizon_stieltjes_grid_partition_exact
    μ f u hu hu0 n
  have hFiniteSum :
      (∫⁻ s in ({0} : Set ℝ), f s ∂μ) +
        ∑ i ∈ Finset.range n, (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ) ≠ ⊤ := by
    rw [← hPartition]
    exact hFinite
  have hFirst :
      (∫⁻ s in ({0} : Set ℝ), f s ∂μ) ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hFiniteSum).1
  have hSum :
      (∑ i ∈ Finset.range n, (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ)) ≠ ⊤ :=
    (ENNReal.add_ne_top.mp hFiniteSum).2
  have hEach :
      ∀ i ∈ Finset.range n,
        (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ) ≠ ⊤ :=
    ENNReal.sum_ne_top.mp hSum
  calc
    (∫⁻ s in Icc (0 : ℝ) (u n), f s ∂μ).toReal =
        ((∫⁻ s in ({0} : Set ℝ), f s ∂μ) +
          ∑ i ∈ Finset.range n,
            (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ)).toReal :=
          congrArg ENNReal.toReal hPartition
    _ = (∫⁻ s in ({0} : Set ℝ), f s ∂μ).toReal +
          ∑ i ∈ Finset.range n,
            (∫⁻ s in Ioc (u i) (u (i + 1)), f s ∂μ).toReal := by
      rw [ENNReal.toReal_add hFirst hSum, ENNReal.toReal_sum hEach]
