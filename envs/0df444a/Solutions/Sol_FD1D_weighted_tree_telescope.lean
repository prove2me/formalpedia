-- Prove2me | solution 1 for FD1D.weighted_tree_telescope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:25.018901+00:00
-- url     : https://prove2.me/submissions/e8fbf035-bac6-4005-ad16-53f6f31c857e

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_weighted_local_sum
import Theorems.Thm_FD1D_FiniteLaw_expect_const
attribute [local simp] FD1D.FiniteLaw.expect_const


attribute [local simp] FD1D.weightedLevel_zero

set_option autoImplicit true
open FD1D
noncomputable section
namespace FD1D
theorem _root_.solution
    (f : ∀ d, DyadicNode d → ℝ) (L : ℕ) :
    ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v * (childAverage f d v - f d v) =
      weightedLevel f L - f 0 dyadicRoot := by
  simp_rw [weighted_local_sum]
  rw [Finset.sum_range_sub]
  rw [weightedLevel_zero]
end FD1D
