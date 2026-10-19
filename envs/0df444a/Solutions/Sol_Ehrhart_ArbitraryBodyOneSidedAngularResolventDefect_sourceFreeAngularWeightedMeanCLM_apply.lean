-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularWeightedMeanCLM_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/055f4d94-94e5-4bf6-937a-694dc11c3e10

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularConstantL2_ae_eq

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
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (f : angularWeightedScalarL2 a) :
    sourceFreeAngularWeightedMeanCLM a f =
      ∫ q : LogTorus n, f q ∂(angularWeightedTorusMeasure a) := by
  change
    @inner ℂ (angularWeightedScalarL2 a) _
      (sourceFreeAngularConstantL2 a 1) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceFreeAngularConstantL2_ae_eq a 1]
    with q hq
  rw [hq, RCLike.inner_apply]
  simp
end Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
