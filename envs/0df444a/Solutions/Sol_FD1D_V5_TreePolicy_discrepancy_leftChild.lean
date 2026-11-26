-- Prove2me | solution 1 for FD1D.V5.TreePolicy.discrepancy_leftChild
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:41:58.237848+00:00
-- url     : https://prove2.me/submissions/c4464f9a-7285-401c-9298-0ef133686e6e

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_leftChild
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.intervalMass_leftChild

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    discrepancy I a (d + 1) (leftChild v) =
      discrepancyLeft a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [discrepancy, intervalMass_leftChild, deletionMass_leftChild]
  rfl
end FD1D.V5.TreePolicy
