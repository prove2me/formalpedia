-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.integral_fderiv_angularSmoothPartition_periodic_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/a9e6a757-9f31-4d0e-81e8-54710e9d413c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_zero_of_le
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_angularSmoothPartitionBump_zero_of_ge
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_hasCompactSupport_angularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_sum_fderiv_angularSmoothPartition_binary_eq_zero
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_angularSmoothPartition_eq_zero_of_zero
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_integral_binaryPeriodic_cutoff_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} (v : Space n)
    {g : Space n → ℂ}
    (hg : Continuous g)
    (hperiod : ∀ (q : Fin n → Bool) (t : Space n),
      g (binaryAngularFundamentalBase q + t) = g t) :
    (∫ t : Space n,
      ((fderiv ℝ (angularSmoothPartition (n := n)) t) v : ℂ) *
        g t ∂(volume : Measure (Space n))) = 0 := by
  let κ : Space n → ℝ :=
    fun t => (fderiv ℝ (angularSmoothPartition (n := n)) t) v
  have hκ : Continuous κ := by
    exact ((contDiff_angularSmoothPartition
      (n := n) (m := 1)).continuous_fderiv
        (by simp)).clm_apply continuous_const
  have hκcompact : HasCompactSupport κ :=
    hasCompactSupport_angularSmoothPartition.fderiv_apply ℝ v
  have houtside : ∀ t : Space n,
      t ∉ Set.univ.pi
        (fun _ : Fin n => Set.Ioc (-1 : ℝ) 1) → κ t = 0 := by
    intro t ht
    have hnot :
        ¬ ∀ i : Fin n, (-1 : ℝ) < t i ∧ t i ≤ 1 := by
      intro h
      apply ht
      intro i _
      exact h i
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hbump : angularSmoothPartitionBump (t i) = 0 := by
      by_cases hleft : t i ≤ -1
      · exact angularSmoothPartitionBump_zero_of_le hleft
      · have hright : 1 < t i := by
          by_contra hn
          apply hi
          exact ⟨lt_of_not_ge hleft, le_of_not_gt hn⟩
        exact angularSmoothPartitionBump_zero_of_ge hright.le
    have hzero : angularSmoothPartition t = 0 := by
      unfold angularSmoothPartition
      exact Finset.prod_eq_zero (Finset.mem_univ i) hbump
    change (fderiv ℝ (angularSmoothPartition (n := n)) t) v = 0
    rw [fderiv_angularSmoothPartition_eq_zero_of_zero hzero]
    rfl
  exact integral_binaryPeriodic_cutoff_eq_zero hκ hκcompact houtside
    (fun t ht0 ht1 =>
      sum_fderiv_angularSmoothPartition_binary_eq_zero t v ht0 ht1)
    hg hperiod
end Ehrhart.MatrixTorusBochnerIdentity
