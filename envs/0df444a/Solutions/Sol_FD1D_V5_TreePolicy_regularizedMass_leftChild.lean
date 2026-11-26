-- Prove2me | solution 1 for FD1D.V5.TreePolicy.regularizedMass_leftChild
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:44:16.314029+00:00
-- url     : https://prove2.me/submissions/3e7e30df-5d33-4b4a-b3e6-667927b89f7e

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.rate_root
attribute [local simp] FD1D.V5.TreePolicy.rate_leftChild
attribute [local simp] FD1D.V5.TreePolicy.rate_rightChild
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_root
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_leftChild
attribute [local simp] FD1D.V5.TreePolicy.intervalMass_rightChild

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    regularizedMass I a (d + 1) (leftChild v) =
      regularizedMassLeft a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  simp [regularizedMass, regularizedMassLeft, inventory]
end FD1D.V5.TreePolicy
