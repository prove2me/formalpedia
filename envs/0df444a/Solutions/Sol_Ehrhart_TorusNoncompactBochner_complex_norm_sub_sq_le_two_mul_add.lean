-- Prove2me | solution 1 for Ehrhart.TorusNoncompactBochner.complex_norm_sub_sq_le_two_mul_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/4dd02559-c42a-4058-8ed9-b8634a64e468

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusNoncompactBochner
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.TorusNoncompactBochner
theorem _root_.solution
    (z w : ℂ) :
    ‖z - w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have hsub := norm_sub_le z w
  have hsq : ‖z - w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hsub
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
end Ehrhart.TorusNoncompactBochner
