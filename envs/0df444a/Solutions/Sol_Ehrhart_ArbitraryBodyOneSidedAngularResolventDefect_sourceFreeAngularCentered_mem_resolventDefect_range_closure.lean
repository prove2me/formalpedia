-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularCentered_mem_resolventDefect_range_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1c2493f5-fb5c-4529-852a-07b0bf877688

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularWeightedMeanZero_le_resolventDefect_range_closure

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
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ}
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : (∫ q : LogTorus n,
      f q ∂(angularWeightedTorusMeasure a)) = 0) :
    f ∈ ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a).range).topologicalClosure := by
  apply sourceFreeAngularWeightedMeanZero_le_resolventDefect_range_closure
    K ha hupper
  exact (mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
    a f).mpr hf
end Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
