-- Prove2me | solution 1 for FD1D.V5.TreePolicy.deterministic_aggregate_estimate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:08:13.513001+00:00
-- url     : https://prove2.me/submissions/2ee3286c-4d80-439e-94a1-771736d4e952

import Definitions.Def_FD1D_V5_LocalBellman
import Definitions.Def_FD1D_V5_TreePolicy
import Theorems.Thm_FD1D_V5_TreePolicy_rate_root
import Theorems.Thm_FD1D_V5_TreePolicy_rate_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_rate_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_root
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_leftChild
import Theorems.Thm_FD1D_V5_TreePolicy_intervalMass_rightChild
import Theorems.Thm_FD1D_V5_TreePolicy_bellmanValue_nonpos
import Theorems.Thm_FD1D_V5_TreePolicy_rateEnergy_root
import Theorems.Thm_FD1D_V5_TreePolicy_local_bellman_inequality_separated
import Theorems.Thm_FD1D_V5_TreePolicy_restoringDrift_div
import Theorems.Thm_FD1D_V5_TreePolicy_bellmanValue_root_lower
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_bellman_tree_telescope
import Theorems.Thm_FD1D_hazard_energy_telescope
import Theorems.Thm_FD1D_nodeMass_nonneg
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
    (ha : 0 < a) (hm : 0 < m) :
    restoringDrift I a ≥
      a / 1000 * hazardEnergy (rate I a) L +
        transportEnergy I a / (1000 * a) -
        501 * a / (1000 * (m : ℝ) ^ 2) := by
  have hsum :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000 +
            imbalance I a d v ^ 2 / (1000 * a ^ 2))) ≤
      ∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (childAverage
              (fun d v => discrepancy I a d v *
                regularizedMass I a d v) d v +
            childAverage (bellmanValue I a) d v -
            bellmanValue I a d v) := by
    apply Finset.sum_le_sum
    intro d hd
    apply Finset.sum_le_sum
    intro v hv
    exact mul_le_mul_of_nonneg_left
      (local_bellman_inequality_separated I ha hm d
        (Finset.mem_range.mp hd) v)
      (nodeMass_nonneg d v)
  have hrate :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
            rate I a d v ^ 2) / 1000)) =
        (hazardEnergy (rate I a) L -
          hazardEnergy (rate I a) 0) / 1000 := by
    calc
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
            rate I a d v ^ 2) / 1000)) =
          (∑ d ∈ Finset.range L,
            ∑ v, nodeMass d v *
              (childAverage (fun d v => rate I a d v ^ 2) d v -
                rate I a d v ^ 2)) / 1000 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro d hd
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro v hv
            ring
      _ = _ := by rw [hazard_energy_telescope]
  have himbalance :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          (imbalance I a d v ^ 2 / (1000 * a ^ 2))) =
        transportEnergy I a / (1000 * a ^ 2) := by
    unfold transportEnergy internalWeightedSum weightedLevel
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro v hv
    ring
  have hright :
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000 +
            imbalance I a d v ^ 2 / (1000 * a ^ 2))) =
        (hazardEnergy (rate I a) L -
            hazardEnergy (rate I a) 0) / 1000 +
          transportEnergy I a / (1000 * a ^ 2) := by
    rw [show
      (∑ d ∈ Finset.range L,
        ∑ v, nodeMass d v *
          ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000 +
            imbalance I a d v ^ 2 / (1000 * a ^ 2))) =
        (∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            ((childAverage (fun d v => rate I a d v ^ 2) d v -
              rate I a d v ^ 2) / 1000)) +
        ∑ d ∈ Finset.range L,
          ∑ v, nodeMass d v *
            (imbalance I a d v ^ 2 / (1000 * a ^ 2)) by
      simp only [mul_add, Finset.sum_add_distrib]]
    rw [hrate, himbalance]
  rw [hright, bellman_tree_telescope] at hsum
  rw [← restoringDrift_div I ha] at hsum
  have hleaf : weightedLevel (bellmanValue I a) L ≤ 0 := by
    apply Finset.sum_nonpos
    intro v hv
    exact mul_nonpos_of_nonneg_of_nonpos
      (nodeMass_nonneg L v)
      (bellmanValue_nonpos I ha hm le_rfl v)
  have hroot :=
    bellmanValue_root_lower I ha hm
  have hH0 :
      hazardEnergy (rate I a) 0 = 1 / (m : ℝ) ^ 2 :=
    rateEnergy_root I a hm
  rw [hH0] at hsum
  have hnegroot :
      -bellmanValue I a 0 dyadicRoot ≤
        1 / (2 * (m : ℝ) ^ 2) := by
    simpa only [neg_neg] using neg_le_neg hroot
  have hsumUpper :
      (hazardEnergy (rate I a) L - 1 / (m : ℝ) ^ 2) / 1000 +
          transportEnergy I a / (1000 * a ^ 2) ≤
        restoringDrift I a / a + 1 / (2 * (m : ℝ) ^ 2) := by
    calc
      (hazardEnergy (rate I a) L - 1 / (m : ℝ) ^ 2) / 1000 +
            transportEnergy I a / (1000 * a ^ 2) ≤
          restoringDrift I a / a +
              weightedLevel (bellmanValue I a) L -
              bellmanValue I a 0 dyadicRoot := hsum
      _ = restoringDrift I a / a +
            weightedLevel (bellmanValue I a) L +
            (-bellmanValue I a 0 dyadicRoot) := by ring
      _ ≤ restoringDrift I a / a + 0 +
            1 / (2 * (m : ℝ) ^ 2) :=
        add_le_add
          (add_le_add (le_refl (restoringDrift I a / a)) hleaf)
          hnegroot
      _ = restoringDrift I a / a +
            1 / (2 * (m : ℝ) ^ 2) := by ring
  have hminus :
      ((hazardEnergy (rate I a) L - 1 / (m : ℝ) ^ 2) / 1000 +
          transportEnergy I a / (1000 * a ^ 2)) -
          1 / (2 * (m : ℝ) ^ 2) ≤
        restoringDrift I a / a :=
    (sub_le_iff_le_add).2 hsumUpper
  have hpre :
      hazardEnergy (rate I a) L / 1000 +
          transportEnergy I a / (1000 * a ^ 2) -
          501 / (1000 * (m : ℝ) ^ 2) ≤
        restoringDrift I a / a := by
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    convert hminus using 1 <;>
      field_simp [hmR] <;> ring
  have hscaled := (le_div_iff₀ ha).mp hpre
  calc
    a / 1000 * hazardEnergy (rate I a) L +
          transportEnergy I a / (1000 * a) -
          501 * a / (1000 * (m : ℝ) ^ 2) =
        (hazardEnergy (rate I a) L / 1000 +
          transportEnergy I a / (1000 * a ^ 2) -
          501 / (1000 * (m : ℝ) ^ 2)) * a := by
            field_simp [ha.ne']
    _ ≤ restoringDrift I a := hscaled
end FD1D.V5.TreePolicy
