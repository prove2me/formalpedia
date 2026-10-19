-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.sum_fderiv_angularSmoothPartition_binary_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/42fc7ba8-97ef-4e8b-821e-c7e4e20fbd39

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartition
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_binaryAngularPartitionSum_eq_zero
import Theorems.Thm_Ehrhart_MatrixTorusBochnerIdentity_fderiv_angularSmoothPartition_translate

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
    {n : ℕ} (t v : Space n)
    (hzero : ∀ i : Fin n, 0 ≤ t i)
    (hone : ∀ i : Fin n, t i ≤ 1) :
    (∑ q : Fin n → Bool,
      (fderiv ℝ (angularSmoothPartition (n := n))
        (binaryAngularFundamentalBase q + t)) v) = 0 := by
  classical
  have hsum :
      fderiv ℝ (binaryAngularPartitionSum n) t =
        ∑ q : Fin n → Bool,
          fderiv ℝ
            (fun s : Space n =>
              angularSmoothPartition
                (binaryAngularFundamentalBase q + s)) t := by
    unfold binaryAngularPartitionSum
    apply fderiv_fun_sum
    intro q _
    exact (contDiff_angularSmoothPartition
      (n := n) (m := 1)).differentiable (by simp)
        (binaryAngularFundamentalBase q + t) |>.comp t (by fun_prop)
  have hzeroDeriv := fderiv_binaryAngularPartitionSum_eq_zero
    t hzero hone
  have happly := congrArg
    (fun A : Space n →L[ℝ] ℝ => A v)
    (hsum.trans (by
      apply Finset.sum_congr rfl
      intro q _
      exact fderiv_angularSmoothPartition_translate
        (binaryAngularFundamentalBase q) t))
  rw [hzeroDeriv] at happly
  simpa using happly.symm
end Ehrhart.MatrixTorusBochnerIdentity
