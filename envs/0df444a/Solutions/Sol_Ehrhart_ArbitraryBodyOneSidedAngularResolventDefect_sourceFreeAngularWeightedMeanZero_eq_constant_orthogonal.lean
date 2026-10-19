-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularWeightedMeanZero_eq_constant_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/31401d70-85a3-44f2-994b-4e7a9e543b23

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularWeightedMeanCLM_apply
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity WeightedTorusDolbeault
open WeightedTorusBrascampLieb ArbitraryBodyOneSidedAngularWeightedKernel
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    sourceFreeAngularWeightedMeanZeroSubmodule a =
      (sourceFreeAngularWeightedConstantSubmodule a)ᗮ := by
  ext f
  rw [mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff]
  change
    (∫ q : LogTorus n,
      f q ∂(angularWeightedTorusMeasure a)) = 0 ↔
      f ∈ (ℂ ∙ sourceFreeAngularConstantL2 a 1)ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [← sourceFreeAngularWeightedMeanCLM_apply]
  rfl
end Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
