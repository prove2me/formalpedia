-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/53fc68ba-ec7a-481e-a1d7-cdb143fe95e4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularResolventDefect_sourceFreeAngularWeightedMeanCLM_apply

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
    f ∈ sourceFreeAngularWeightedMeanZeroSubmodule a ↔
      (∫ q : LogTorus n,
        f q ∂(angularWeightedTorusMeasure a)) = 0 := by
  change sourceFreeAngularWeightedMeanCLM a f = 0 ↔ _
  rw [sourceFreeAngularWeightedMeanCLM_apply]
end Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
