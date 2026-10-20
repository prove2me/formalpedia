-- Prove2me | solution 1 for AvramDividend.Classical.recordPartition_pointwise_tsum_indicator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T21:17:19.1515+00:00
-- url     : https://prove2.me/submissions/03b457fb-64ea-46d8-bf25-133d9c930bc5

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorems.Thm_AvramDividend_Classical_recordPartition_Ioc_disjoint
import Theorems.Thm_AvramDividend_Classical_recordPartition_countable_cover_iff

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
open AvramDividend.Classical

theorem solution
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (r : ℝ) (c : ℝ≥0∞) :
    (∑' i : ℕ,
      if r ∈ Set.Ioc (u i) (u (i + 1)) then c else 0) =
      if u 0 < r then c else 0 := by
  classical
  by_cases hr : u 0 < r
  · obtain ⟨i, hi⟩ :=
      (recordPartition_countable_cover_iff u hu hcofinal r).mp hr
    have hSingle :
        (∑' j : ℕ,
          if r ∈ Set.Ioc (u j) (u (j + 1)) then c else 0) =
          (if r ∈ Set.Ioc (u i) (u (i + 1)) then c else 0) := by
      apply tsum_eq_single i
      intro j hji
      have hjnot : r ∉ Set.Ioc (u j) (u (j + 1)) := by
        intro hj
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · exact (Set.disjoint_left.mp
            (recordPartition_Ioc_disjoint u hu j i hlt)) hj hi
        · exact (Set.disjoint_left.mp
            (recordPartition_Ioc_disjoint u hu i j hgt)) hi hj
      simp [hjnot]
    rw [hSingle]
    simp [hi, hr]
  · have hNone (i : ℕ) :
        r ∉ Set.Ioc (u i) (u (i + 1)) := by
      intro hi
      exact hr
        ((recordPartition_countable_cover_iff u hu hcofinal r).mpr ⟨i, hi⟩)
    simp [hNone, hr]
