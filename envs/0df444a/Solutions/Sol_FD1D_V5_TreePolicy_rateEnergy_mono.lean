-- Prove2me | solution 1 for FD1D.V5.TreePolicy.rateEnergy_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:12.97622+00:00
-- url     : https://prove2.me/submissions/7e1de5b1-e618-4c92-9a8e-6d4b3ad03694

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_local_rate_energy_nonneg
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_nodeMass_nonneg
import Theorems.Thm_FD1D_weightedLevel_zero
import Theorems.Thm_FD1D_weighted_local_sum
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
    {d : ℕ} (hdL : d < L) :
    hazardEnergy (rate I a) d ≤ hazardEnergy (rate I a) (d + 1) := by
  have hsum :
      0 ≤ ∑ v, nodeMass d v *
        (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2) := by
    apply Finset.sum_nonneg
    intro v _
    exact mul_nonneg (nodeMass_nonneg d v)
      (local_rate_energy_nonneg I ha hm d hdL v)
  rw [weighted_local_sum] at hsum
  exact sub_nonneg.mp (by simpa [hazardEnergy] using hsum)
end FD1D.V5.TreePolicy
