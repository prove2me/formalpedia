-- Prove2me | solution 1 for FD1D.V5.TreePolicy.deletionMass_children
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:50:10.787958+00:00
-- url     : https://prove2.me/submissions/6f7382da-a0d6-4e2e-9066-448afc76727b

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_rightChild
import Theorems.Thm_FD1D_V5_LocalPolicy_massLeft_add_massRight


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    deletionMass I a d v =
      deletionMass I a (d + 1) (leftChild v) +
        deletionMass I a (d + 1) (rightChild v) := by
  rw [deletionMass_leftChild, deletionMass_rightChild,
    massLeft_add_massRight]
  unfold deletionMass parentMass inventory LocalPolicy.inventory
  rw [I.count_children d hdL v]
  norm_num
end FD1D.V5.TreePolicy
