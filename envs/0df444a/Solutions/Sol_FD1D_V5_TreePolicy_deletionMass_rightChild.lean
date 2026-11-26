-- Prove2me | solution 1 for FD1D.V5.TreePolicy.deletionMass_rightChild
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:39:22.538246+00:00
-- url     : https://prove2.me/submissions/16192462-b4e7-486b-b95a-aa9830397678

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_massRight_eq_count_mul_rateRight
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.rate_rightChild

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (v : DyadicNode d) :
    deletionMass I a (d + 1) (rightChild v) =
      massRight a (intervalMass d v) (rate I a d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  rw [deletionMass, inventory, rate_rightChild]
  exact (massRight_eq_count_mul_rateRight _ _ _ _ _).symm
end FD1D.V5.TreePolicy
