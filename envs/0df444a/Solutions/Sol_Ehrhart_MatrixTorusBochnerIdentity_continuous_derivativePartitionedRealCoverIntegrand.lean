-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.continuous_derivativePartitionedRealCoverIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/644533a8-0390-42bb-8701-e6d65e2b86d4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_angularSmoothPartition

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
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f)
    (v : Space n) :
    Continuous (derivativePartitionedRealCoverIntegrand φ f v) := by
  have hder : Continuous
      (fun t : Space n =>
        (fderiv ℝ (angularSmoothPartition (n := n)) t) v) :=
    ((contDiff_angularSmoothPartition
      (n := n) (m := 1)).continuous_fderiv
        (by simp)).clm_apply continuous_const
  unfold derivativePartitionedRealCoverIntegrand
  apply (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (hφ.comp continuous_fst).neg)).mul
  apply (Complex.continuous_ofReal.comp
    (hder.comp continuous_snd)).mul
  exact hf.comp
    (continuous_fst.prodMk
      ((continuous_angularCoverProjection n).comp continuous_snd))
end Ehrhart.MatrixTorusBochnerIdentity
