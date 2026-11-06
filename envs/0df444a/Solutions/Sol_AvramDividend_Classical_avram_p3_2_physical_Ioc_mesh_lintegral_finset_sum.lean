-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_2_physical_Ioc_mesh_lintegral_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:02:09.974283+00:00
-- url     : https://prove2.me/submissions/42fde30a-b57c-4ba4-90f5-19db6621e76c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_monotone_Ioc_mesh_cover

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- The exact nonnegative Stieltjes mass on a monotone physical time
interval is the sum of the masses of its finite disjoint Ioc cells. -/
theorem solution (μ : Measure ℝ) (u : ℕ → ℝ)
    (hu : Monotone u) (n : ℕ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in Ioc (u 0) (u n), f t ∂μ) =
      ∑ i ∈ Finset.range n,
        ∫⁻ t in Ioc (u i) (u (i + 1)), f t ∂μ := by
  let A : ℕ → Set ℝ := fun i => Ioc (u i) (u (i + 1))
  have hd : Set.PairwiseDisjoint (↑(Finset.range n) : Set ℕ) A := by
    intro i hi j hj hij
    change Disjoint (Ioc (u i) (u (i + 1)))
      (Ioc (u j) (u (j + 1)))
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hstep : i + 1 ≤ j := Nat.succ_le_iff.mpr hlt
      have hle : u (i + 1) ≤ u j := hu hstep
      exact (not_lt_of_ge (le_trans hxi.2 hle)) hxj.1
    · have hstep : j + 1 ≤ i := Nat.succ_le_iff.mpr hgt
      have hle : u (j + 1) ≤ u i := hu hstep
      exact (not_lt_of_ge (le_trans hxj.2 hle)) hxi.1
  have hm : ∀ i ∈ Finset.range n, MeasurableSet (A i) := by
    intro i hi
    exact measurableSet_Ioc
  have hsum :=
    MeasureTheory.lintegral_biUnion_finset (μ := μ) hd hm f
  have hcover :=
    avram_p3_2_physical_monotone_Ioc_mesh_cover u hu n
  rw [← hcover]
  simpa only [A] using hsum
