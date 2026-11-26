-- Prove2me | solution 1 for FD1D.V5.TreePolicy.intervalMass_le_count_add_half_mul_rate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:07:40.489576+00:00
-- url     : https://prove2.me/submissions/6602c6a8-e9c4-44ed-b302-2ac5a799e940

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_le_rate
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
theorem _root_.solution
    (I : AggregatedInventory L m) {a : ℝ}
    (ha : 0 < a) (hm : 0 < m)
    {d : ℕ} (hdL : d ≤ L) (v : DyadicNode d) :
    intervalMass d v ≤
      (inventory I d v + a / 2) * rate I a d v := by
  have hden : 0 < inventory I d v + a / 2 := by
    unfold inventory
    positivity
  have hreg := regularizedMass_le_rate I ha hm hdL v
  unfold regularizedMass at hreg
  simpa [mul_comm] using (div_le_iff₀ hden).mp hreg
end FD1D.V5.TreePolicy
