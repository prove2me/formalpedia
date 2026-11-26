-- Prove2me | solution 1 for FD1D.globalHarmonicPotential_le_log_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:24:27.667544+00:00
-- url     : https://prove2.me/submissions/303dad41-562a-4761-b2df-2b591472300b

import Definitions.Def_FD1D_Potential
import Definitions.Def_FD1D_Parameters
import Definitions.Def_FD1D_PotentialBounds
import Theorems.Thm_FD1D_harmonicPotential_le_log_one_add
import Theorems.Thm_FD1D_FiniteLaw_expect_const
import Theorems.Thm_FD1D_harmonicPotential_zero
import Theorems.Thm_FD1D_leafCount_eq_pow
import Theorems.Thm_FD1D_natFloor_parameterRatio
import Theorems.Thm_FD1D_policyA_eq_parameterA
import Theorems.Thm_FD1D_sum_nonroot_nodeMass_sq
import Theorems.Thm_FD1D_weightedLevel_zero
attribute [local simp] FD1D.FiniteLaw.expect_const
attribute [local simp] FD1D.harmonicPotential_zero
attribute [local simp] FD1D.leafCount_eq_pow
attribute [local simp] FD1D.natFloor_parameterRatio
attribute [local simp] FD1D.policyA_eq_parameterA
attribute [local simp] FD1D.weightedLevel_zero



set_option autoImplicit true
open FD1D
noncomputable section
open Set intervalIntegral
open scoped BigOperators
namespace FD1D
theorem _root_.solution
    {L m : ℕ} {a : ℝ} {N : ∀ d, DyadicNode d → ℕ}
    (ha : 0 < a) (hN : ∀ d v, N d v ≤ m) :
    globalHarmonicPotential L a N ≤
      Real.log (1 + (m : ℝ) / a) := by
  have hquot : 0 ≤ (m : ℝ) / a :=
    div_nonneg (Nat.cast_nonneg m) ha.le
  have harg : (1 : ℝ) ≤ 1 + (m : ℝ) / a := by linarith
  have hlog : 0 ≤ Real.log (1 + (m : ℝ) / a) :=
    Real.log_nonneg harg
  have hnode (d : ℕ) (v : DyadicNode d) :
      harmonicPotential a (N d v) ≤ Real.log (1 + (m : ℝ) / a) := by
    calc
      harmonicPotential a (N d v) ≤
          Real.log (1 + (N d v : ℝ) / a) :=
        harmonicPotential_le_log_one_add ha _
      _ ≤ Real.log (1 + (m : ℝ) / a) := by
        apply Real.strictMonoOn_log.monotoneOn
        · exact Set.mem_Ioi.mpr (by positivity)
        · exact Set.mem_Ioi.mpr (by positivity)
        · have hcast : (N d v : ℝ) ≤ (m : ℝ) :=
            Nat.cast_le.mpr (hN d v)
          simpa [add_comm] using
            add_le_add_left
              (div_le_div_of_nonneg_right hcast ha.le) 1
  calc
    globalHarmonicPotential L a N ≤
        nonrootMassSqSum L * Real.log (1 + (m : ℝ) / a) := by
      unfold globalHarmonicPotential nonrootMassSqSum
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro d hd
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro v hv
      exact mul_le_mul_of_nonneg_left (hnode _ _) (sq_nonneg _)
    _ ≤ Real.log (1 + (m : ℝ) / a) := by
      rw [sum_nonroot_nodeMass_sq]
      have hpow : 0 < (2 : ℝ) ^ L := by positivity
      nlinarith [one_div_pos.mpr hpow]
end FD1D
