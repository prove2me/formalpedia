-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.continuous_partitionedRealCoverIntegrand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/fa6a43ef-20fc-4dfa-b778-8395b95063cc

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
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f) :
    Continuous (partitionedRealCoverIntegrand φ f) := by
  unfold partitionedRealCoverIntegrand
  apply (Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (hφ.comp continuous_fst).neg)).mul
  apply (Complex.continuous_ofReal.comp
    ((contDiff_angularSmoothPartition (m := 0)).continuous.comp
      continuous_snd)).mul
  exact hf.comp
    (continuous_fst.prodMk
      ((continuous_angularCoverProjection n).comp continuous_snd))
end Ehrhart.MatrixTorusBochnerBridge
