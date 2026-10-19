-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularWeakScalarResolventCLM_fixed_ae_eq_const_of_support_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/def07b26-e2f6-4272-ab5e-66c1a905ca3d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBrascampLieb_angularWeakScalarResolventCLM_fixed_iff_graph_zero
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularZeroGraph_ae_constant_of_support_upper

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : angularWeakScalarResolventCLM a f = f) :
    ∃ c : ℂ,
      (fun q : LogTorus n => f q) =ᵐ[
        angularWeightedTorusMeasure a] (fun _ => c) :=
  angularZeroGraph_ae_constant_of_support_upper K ha hupper f
    ((angularWeakScalarResolventCLM_fixed_iff_graph_zero a f).mp hf)
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
