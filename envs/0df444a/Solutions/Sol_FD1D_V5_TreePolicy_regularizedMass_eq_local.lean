-- Prove2me | solution 1 for FD1D.V5.TreePolicy.regularizedMass_eq_local
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:50:43.949457+00:00
-- url     : https://prove2.me/submissions/412cf261-9d95-4c2e-a65e-70f9fa7c4d7f

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
section
namespace FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
private theorem parent_local_data
    (I : AggregatedInventory L m) (a : ℝ)
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    let x := I.count (d + 1) (leftChild v)
    let y := I.count (d + 1) (rightChild v)
    inventory I d v = LocalPolicy.inventory x y ∧
      deletionMass I a d v =
        parentMass (rate I a d v) x y := by
  dsimp
  have hc := I.count_children d hdL v
  constructor <;>
    simp [inventory, deletionMass, parentMass, LocalPolicy.inventory, hc]
end
end FD1D.V5.TreePolicy
end

set_option autoImplicit true
open FD1D FD1D.V5 FD1D.V5.TreePolicy
noncomputable section
open LocalPolicy
variable {L m : ℕ}
namespace FD1D.V5.TreePolicy
theorem _root_.solution (I : AggregatedInventory L m)
    (a : ℝ) (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    regularizedMass I a d v =
      LocalPolicy.regularizedMass a (intervalMass d v)
        (I.count (d + 1) (leftChild v))
        (I.count (d + 1) (rightChild v)) := by
  unfold regularizedMass LocalPolicy.regularizedMass
  rw [(parent_local_data I a d hdL v).1]
end FD1D.V5.TreePolicy
