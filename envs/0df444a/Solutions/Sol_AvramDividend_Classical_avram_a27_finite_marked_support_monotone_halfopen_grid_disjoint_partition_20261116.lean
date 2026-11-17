-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_finite_marked_support_monotone_halfopen_grid_disjoint_partition_20261116
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T09:12:30.503819+00:00
-- url     : https://prove2.me/submissions/229269eb-9283-49c9-b43e-b5ffe5e79286

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_monotone_halfopen_grid_interval_partition_20261116
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ)
    (S : Finset ℝ≥0)
    (hS : ∀ t ∈ S, t ∈ Ioc (u 0) (u n)) :
    let F : ℕ → Finset ℝ≥0 := fun i =>
      S.filter (fun t => t ∈ Ioc (u i) (u (i + 1)))
    (Finset.range n).biUnion F = S ∧
      ((Finset.range n : Set ℕ).PairwiseDisjoint F) := by
  classical
  let F : ℕ → Finset ℝ≥0 := fun i =>
    S.filter (fun t => t ∈ Ioc (u i) (u (i + 1)))
  change (Finset.range n).biUnion F = S ∧
    ((Finset.range n : Set ℕ).PairwiseDisjoint F)
  constructor
  · ext t
    simp only [Finset.mem_biUnion, F, Finset.mem_filter]
    constructor
    · rintro ⟨i, hi, hti, hcell⟩
      exact hti
    · intro ht
      have hc : t ∈ ⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1)) := by
        rw [avram_a26_monotone_halfopen_grid_interval_partition_20261116 u hu n]
        exact hS t ht
      rcases Set.mem_iUnion.mp hc with ⟨i, hi'⟩
      rcases Set.mem_iUnion.mp hi' with ⟨hi, hcell⟩
      exact ⟨i, hi, ht, hcell⟩
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro t hit hjt
    have hi' := (Finset.mem_filter.mp hit).2
    have hj' := (Finset.mem_filter.mp hjt).2
    rcases lt_or_gt_of_ne hij with h | h
    · have hle : u (i + 1) ≤ u j := hu (Nat.succ_le_iff.mpr h)
      exact (not_lt_of_ge (hi'.2.trans hle)) hj'.1
    · have hle : u (j + 1) ≤ u i := hu (Nat.succ_le_iff.mpr h)
      exact (not_lt_of_ge (hj'.2.trans hle)) hi'.1
