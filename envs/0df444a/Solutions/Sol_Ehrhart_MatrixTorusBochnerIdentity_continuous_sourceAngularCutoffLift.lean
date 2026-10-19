-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.continuous_sourceAngularCutoffLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/4b8a2154-e3a3-41fa-b670-67dbaf3e3827

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_contDiff_coverAngularSmoothPartition

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
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : Continuous f) :
    Continuous (sourceAngularCutoffLift f) := by
  unfold sourceAngularCutoffLift
  exact (Complex.continuous_ofReal.comp
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := 1)).continuous).mul
        (hf.comp (continuous_complexTorusCoverProjection n))
end Ehrhart.MatrixTorusBochnerIdentity
