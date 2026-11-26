-- Prove2me | solution 1 for FD1D.V5.TreePolicy.regularizedMass_rightChild
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:44:44.736855+00:00
-- url     : https://prove2.me/submissions/159f01a9-1e4e-456e-8c8e-79fee97f5ba6

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
    regularizedMass I a (d + 1) (rightChild v) =
      regularizedMassRight a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  simp [regularizedMass, regularizedMassRight, inventory]
end FD1D.V5.TreePolicy
