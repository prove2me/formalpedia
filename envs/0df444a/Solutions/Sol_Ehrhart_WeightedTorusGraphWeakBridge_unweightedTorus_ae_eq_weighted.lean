-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.unweightedTorus_ae_eq_weighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/78d4b136-02ed-4f75-9524-c78c10c68ba2

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusGraphWeakBridge_weightedTorus_ae_iff_unweighted

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusGraphWeakBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge
open WeightedTorusDistributionBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.WeightedTorusGraphWeakBridge
theorem _root_.solution {n k : ℕ}
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g) :
    f =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ] g :=
  (weightedTorus_ae_iff_unweighted hφ (fun z => f z = g z)).mpr h
end Ehrhart.WeightedTorusGraphWeakBridge
