-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousClosedResolventAdjoint.contDiff_translatedDensityCancelledCoverKernel_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/632c3726-8e3e-4ffd-9351-01ba40265e97

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeight_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousClosedResolventAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb TorusWeakDolbeaultMollification TorusFriedrichsMollifierEstimates
open TorusMollifiedBochner TorusWeightedAdjointMollification
open TorusWeightedDensityConvolutionDivergence TorusClosedMollifierAdjoint
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusHomogeneousClosedResolventAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (k : ℕ) (x : LogSpace n) :
    ContDiff ℝ 3 (translatedDensityCancelledCoverKernel a k x) := by
  unfold translatedDensityCancelledCoverKernel
  exact ((complexShrinkingBump (n := n) k).contDiff_normed.comp
    (contDiff_const.sub contDiff_id)).div
      ha3.neg.exp
      (fun y => (coverWeight_pos (angularCoverPotential a) y).ne')
end Ehrhart.TorusHomogeneousClosedResolventAdjoint
