-- Prove2me | solution 1 for FD1D.V5.TreePolicy.imbalance_eq_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:52:08.342387+00:00
-- url     : https://prove2.me/submissions/5fa478ba-e0b7-430f-bdfa-2b55dcd31cf6

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_deletionMass_rightChild
import Theorems.Thm_FD1D_V5_LocalPolicy_bias_eq_massLeft_sub_massRight


set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    imbalance I a d v =
      bias a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  unfold imbalance
  rw [deletionMass_leftChild, deletionMass_rightChild]
  exact (bias_eq_massLeft_sub_massRight _ _ _ _ _).symm
end FD1D.V5.TreePolicy
