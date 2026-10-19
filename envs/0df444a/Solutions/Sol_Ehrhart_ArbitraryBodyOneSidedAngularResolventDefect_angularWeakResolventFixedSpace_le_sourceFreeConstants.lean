-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect.angularWeakResolventFixedSpace_le_sourceFreeConstants
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/05832849-57e3-496f-9f59-df961443562a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularWeakScalarResolventCLM_fixed_ae_eq_const_of_support_upper
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
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ}
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C) :
    angularWeakResolventFixedSpace a ≤
      sourceFreeAngularWeightedConstantSubmodule a := by
  intro f hf
  change angularWeakScalarResolventCLM a f = f at hf
  obtain ⟨c, hc⟩ :=
    angularWeakScalarResolventCLM_fixed_ae_eq_const_of_support_upper
      K ha hupper f hf
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul c
      (sourceFreeAngularConstantL2 a 1),
    sourceFreeAngularConstantL2_ae_eq a 1, hc]
      with q hsmul hone hconstant
  rw [hsmul]
  change c * sourceFreeAngularConstantL2 a 1 q = f q
  rw [hone, hconstant]
  simp
end Ehrhart.ArbitraryBodyOneSidedAngularResolventDefect
