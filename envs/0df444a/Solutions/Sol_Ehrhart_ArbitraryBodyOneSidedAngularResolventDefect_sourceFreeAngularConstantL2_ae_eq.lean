-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.sourceFreeAngularConstantL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/75c00d08-df92-46f8-8a01-3b1097c1416a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (c : ℂ) :
    (fun q : LogTorus n => sourceFreeAngularConstantL2 a c q) =ᵐ[
      angularWeightedTorusMeasure a] (fun _ => c) :=
  MeasureTheory.MemLp.coeFn_toLp
    (memLp_const (μ := angularWeightedTorusMeasure a)
      (p := 2) c)
end Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
