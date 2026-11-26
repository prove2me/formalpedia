-- Prove2me | solution 1 for FD1D.V5.TreePolicy.local_rate_energy_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:01:34.866608+00:00
-- url     : https://prove2.me/submissions/a8d7448d-a653-4a16-84c6-380e843326f1

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_pos
import Theorems.Thm_FD1D_V5_TreePolicy_local_rate_average_ge
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
    (d : ℕ) (hdL : d < L) (v : DyadicNode d) :
    0 ≤ childAverage (fun d v => rate I a d v ^ 2) d v -
      rate I a d v ^ 2 := by
  let hL := rate I a (d + 1) (leftChild v)
  let hR := rate I a (d + 1) (rightChild v)
  let hP := rate I a d v
  let avg := (hL + hR) / 2
  have havg : hP ≤ avg := by
    simpa [hP, avg, hL, hR, childAverage] using
      local_rate_average_ge I ha hm d hdL v
  have hp : 0 < hP := rate_pos I ha hm (by omega) v
  have havg0 : 0 ≤ avg := hp.le.trans havg
  have hJensen :
      avg ^ 2 ≤ (hL ^ 2 + hR ^ 2) / 2 := by
    dsimp [avg]
    nlinarith [sq_nonneg (hL - hR)]
  have hmono : hP ^ 2 ≤ avg ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr havg)
      (add_nonneg havg0 hp.le)]
  unfold childAverage
  dsimp [hL, hR, hP] at *
  linarith
end FD1D.V5.TreePolicy
