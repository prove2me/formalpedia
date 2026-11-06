-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_marked_count_arbitrary_grid_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:36:29.606865+00:00
-- url     : https://prove2.me/submissions/43c948e8-f20d-45a1-934c-f1a5905a8ff9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original negative mark counts telescope on a physical grid with arbitrary positive start. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (grid : ℕ → ℝ≥0)
    (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (B : Set ℝ) (hB : MeasurableSet B) (n : ℕ) :
    let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (I ×ˢ B)
    (∑ i ∈ Finset.range n, J (Ioc (grid i) (grid (i + 1)))) =
      J (Ioc (grid 0) (grid n)) := by
  classical
  let J : Set ℝ≥0 → ℝ≥0∞ := fun I =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (I ×ˢ B)
  change (∑ i ∈ Finset.range n, J (Ioc (grid i) (grid (i + 1)))) =
    J (Ioc (grid 0) (grid n))
  have hFrom0 (k : ℕ) : grid 0 ≤ grid k := by
    induction k with
    | zero => exact le_rfl
    | succ j hj => exact hj.trans (hGrid j)
  induction n with
  | zero =>
      simp [J]
  | succ k ih =>
      have hSplit :=
        avram_p4_s3_run1640_original_intrinsic_marked_general_interval_partition
          X ω (grid 0) (grid k) (grid (k + 1)) (hFrom0 k) (hGrid k) B hB
      change J (Ioc (grid 0) (grid (k + 1))) =
        J (Ioc (grid 0) (grid k)) + J (Ioc (grid k) (grid (k + 1))) at hSplit
      rw [Finset.sum_range_succ, ih]
      exact hSplit.symm
