-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.contDiff_sourceAngularCutoffLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/ab41ea53-8f7e-4884-b734-5b84422e2b59

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
    {n : ℕ} {m : ℕ∞}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    (hf : ContDiff ℝ m (complexTorusCoverLift f)) :
    ContDiff ℝ m (sourceAngularCutoffLift f) := by
  change ContDiff ℝ m
    (fun z : TorusCharacters.LogSpace n =>
      (coverAngularSmoothPartition z : ℂ) *
        complexTorusCoverLift f z)
  exact (Complex.ofRealCLM.contDiff.comp
    (contDiff_coverAngularSmoothPartition
      (n := n) (m := m))).mul hf
end Ehrhart.MatrixTorusBochnerIdentity
