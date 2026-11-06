-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_grid_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:20:39.259632+00:00
-- url     : https://prove2.me/submissions/0413bc00-a27a-4aa8-b8db-601738281fc0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Exact original physical negative-jump counts telescope along finite physical time grids. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (hZero : grid 0 = 0)
    (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    (∑ i ∈ Finset.range n, J (Ioc (grid i) (grid (i + 1)))) =
      J (Ioc 0 (grid n)) := by
  classical
  let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (I ×ˢ B)
  change (∑ i ∈ Finset.range n, J (Ioc (grid i) (grid (i + 1)))) =
    J (Ioc 0 (grid n))
  induction n with
  | zero =>
      simp [hZero, J]
  | succ n ih =>
      have hSplit :=
        avram_p4_s3_run1640_original_intrinsic_negative_marked_time_partition
          X ω (grid n) (grid (n + 1)) (hGrid n) B hB
      change J (Ioc 0 (grid (n + 1))) =
        J (Ioc 0 (grid n)) + J (Ioc (grid n) (grid (n + 1))) at hSplit
      rw [Finset.sum_range_succ, ih]
      exact hSplit.symm
