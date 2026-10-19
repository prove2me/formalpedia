-- Prove2me | solution 1 for Ehrhart.TorusClosedMollifierAdjoint.contDiff_translatedDensityCancelledCoverKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/d56b27d5-ae78-4788-9742-2ce6cc7f7e96

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeight_pos
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_contDiff_coverWeight

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusClosedMollifierAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open TorusDensityAdaptedWeightedAdjoint
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusClosedMollifierAdjoint
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 1 (angularCoverPotential a))
    (k : ℕ) (x : LogSpace n) :
    ContDiff ℝ 1 (translatedDensityCancelledCoverKernel a k x) := by
  unfold translatedDensityCancelledCoverKernel
  exact ((complexShrinkingBump (n := n) k).contDiff_normed.comp
    (contDiff_const.sub contDiff_id)).div
      (contDiff_coverWeight ha)
      (fun y => (coverWeight_pos (angularCoverPotential a) y).ne')
end Ehrhart.TorusClosedMollifierAdjoint
