-- Prove2me | solution 1 for FD1D.V5.TreePolicy.local_bellman_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:58:51.904041+00:00
-- url     : https://prove2.me/submissions/f836d627-1daa-42a2-964c-5d5b63a1cf77

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_eq_local
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_eq_local
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_regularizedMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_pos
import Theorems.Thm_FD1D_V5_TreePolicy_discrepancy_le_half
import Theorems.Thm_FD1D_V5_TreePolicy_imbalance_eq_local
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_V5_LocalBellman_local_bellman_inequality
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
    childAverage
          (fun d v => discrepancy I a d v *
            regularizedMass I a d v) d v +
        childAverage (bellmanValue I a) d v -
        bellmanValue I a d v ≥
      (childAverage (fun d v => rate I a d v ^ 2) d v -
          rate I a d v ^ 2 +
          imbalance I a d v ^ 2 / a ^ 2) / 1000 := by
  let x := I.count (d + 1) (leftChild v)
  let y := I.count (d + 1) (rightChild v)
  have hh := rate_pos I ha hm (by omega) v
  have ht := discrepancy_le_half I ha hm (by omega) v
  rw [discrepancy_eq_local I a d hdL v] at ht
  have hlocal :=
    LocalBellman.local_bellman_inequality ha
      (nodeMass_pos d v) hh ht
  unfold LocalBellman.localResidual LocalBellman.localEnergy at hlocal
  have hdiscL :
      discrepancyLeft a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        discrepancy I a (d + 1) (leftChild v) :=
    (discrepancy_leftChild I a d v).symm
  have hdiscR :
      discrepancyRight a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        discrepancy I a (d + 1) (rightChild v) :=
    (discrepancy_rightChild I a d v).symm
  have hZL :
      regularizedMassLeft a (nodeMass d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        regularizedMass I a (d + 1) (leftChild v) :=
    (regularizedMass_leftChild I a d v).symm
  have hZR :
      regularizedMassRight a (nodeMass d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        regularizedMass I a (d + 1) (rightChild v) :=
    (regularizedMass_rightChild I a d v).symm
  have hrateL :
      rateLeft a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        rate I a (d + 1) (leftChild v) :=
    (rate_leftChild I a d v).symm
  have hrateR :
      rateRight a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        rate I a (d + 1) (rightChild v) :=
    (rate_rightChild I a d v).symm
  have hdiscP :
      LocalPolicy.discrepancy a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        discrepancy I a d v :=
    (discrepancy_eq_local I a d hdL v).symm
  have hZP :
      LocalPolicy.regularizedMass a (nodeMass d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        regularizedMass I a d v :=
    (regularizedMass_eq_local I a d hdL v).symm
  have hb :
      bias a (nodeMass d v) (rate I a d v)
          (I.count (d + 1) (leftChild v))
          (I.count (d + 1) (rightChild v)) =
        imbalance I a d v :=
    (imbalance_eq_local I a d v).symm
  rw [hdiscL, hdiscR, hZL, hZR, hrateL, hrateR,
    hdiscP, hZP, hb] at hlocal
  unfold childAverage bellmanValue
  ring_nf at hlocal ⊢
  exact hlocal
end FD1D.V5.TreePolicy
