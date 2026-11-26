-- Prove2me | solution 1 for FD1D.bellman_tree_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:03:16.627062+00:00
-- url     : https://prove2.me/submissions/0343c839-6ccd-4493-b84c-f632c1d45983

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_weighted_childAverage_sum
import Theorems.Thm_FD1D_weighted_local_sum
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (c B : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage c d v + childAverage B d v - B d v) =
      nonrootWeightedSum c L + weightedLevel B L - B 0 dyadicRoot := by
  have hlevel : ∀ d,
      (∑ v, nodeMass d v *
        (childAverage c d v + childAverage B d v - B d v)) =
        weightedLevel c (d + 1) +
          (weightedLevel B (d + 1) - weightedLevel B d) := by
    intro d
    rw [show (∑ v, nodeMass d v *
        (childAverage c d v + childAverage B d v - B d v)) =
        (∑ v, nodeMass d v * childAverage c d v) +
        ∑ v, nodeMass d v * (childAverage B d v - B d v) by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro v _
          ring]
    rw [weighted_childAverage_sum, weighted_local_sum]
  simp_rw [hlevel]
  rw [Finset.sum_add_distrib, Finset.sum_range_sub]
  rw [weightedLevel_zero]
  simp only [nonrootWeightedSum]
  ring
end FD1D
