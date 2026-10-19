-- Prove2me | solution 1 for Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel.angularZeroGraph_ae_constant_of_support_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/2469b53f-0b32-4ed8-aa69-dd4a00f86fbd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusBrascampLieb_radialZeroGraph_weightOne_ae_constant
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularToRadialLpOfUpper_ae_eq
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_angularZeroGraph_mem_radialZeroGraph_of_upper
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_radial_ae_iff_angular_of_continuous
import Theorems.Thm_Ehrhart_ArbitraryBodyOneSidedAngularWeightedKernel_smoothConvexPotential_upper_of_support_upper

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
    (hf : WithLp.toLp 2
      (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a) :
    ∃ c : ℂ,
      (fun q : LogTorus n => f q) =ᵐ[
        angularWeightedTorusMeasure a]
          (fun _ => c) := by
  let φ := smoothConvexPotential K
  have hφ : Continuous φ :=
    (smoothConvexPotential_contDiff K).continuous
  have hb : ∀ x : Space n,
      |φ x -
        SupportFunction.supportFunction K.carrier x| ≤ 1 :=
    smoothConvexPotential_bounded K
  have hcomparison : ∀ q : LogTorus n,
      a q ≤ φ q.1 + (C + 1) :=
    smoothConvexPotential_upper_of_support_upper K hupper
  have hgraph :=
    angularZeroGraph_mem_radialZeroGraph_of_upper
      hφ hcomparison f hf
  obtain ⟨c, hc⟩ :=
    radialZeroGraph_weightOne_ae_constant
      K hφ hb
      (angularToRadialLpOfUpper hφ hcomparison f)
      hgraph
  refine ⟨c, (radial_ae_iff_angular_of_continuous
    ha hφ (fun q : LogTorus n => f q = c)).mp ?_⟩
  filter_upwards [
    angularToRadialLpOfUpper_ae_eq hφ hcomparison f, hc]
      with q htransfer hconstant
  exact htransfer.symm.trans hconstant
end Ehrhart.ArbitraryBodyOneSidedAngularWeightedKernel
