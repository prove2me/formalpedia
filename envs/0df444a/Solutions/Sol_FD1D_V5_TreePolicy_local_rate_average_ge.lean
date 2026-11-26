-- Prove2me | solution 1 for FD1D.V5.TreePolicy.local_rate_average_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:50.239203+00:00
-- url     : https://prove2.me/submissions/f92076bb-b562-4214-8c6d-3f18dd448ac9

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_eq_local
import Theorems.Thm_FD1D_V5_TreePolicy_rate_pos
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_le_half
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalPolicy_child_rate_average_ge
import Theorems.Thm_FD1D_nodeMass_pos
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.weightedLevel_zero


attribute [local simp] FD1D.V5.TreePolicy.rate_leftChild
attribute [local simp] FD1D.V5.TreePolicy.rate_rightChild

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    rate I a d v ≤
      childAverage (rate I a) d v := by
  have hp : 0 < intervalMass d v := nodeMass_pos d v
  have hh := rate_pos I ha hm (by omega) v
  have ht := discrepancy_le_half I ha hm (by omega) v
  rw [discrepancy_eq_local I a d hdL v] at ht
  have hlocal :=
    LocalPolicy.child_rate_average_ge ha hp hh ht
  unfold childAverage
  rw [rate_leftChild, rate_rightChild]
  exact hlocal
end FD1D.V5.TreePolicy
