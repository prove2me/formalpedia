-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.weightedTorus_ae_iff_unweighted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/64fe618e-9ee9-4351-a9c9-128234dae4b8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_radialWeight_pos
import Theorems.Thm_Ehrhart_WeightedTorusDistributionBridge_weightedTorusMeasure_eq_unweighted_withDensity

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
    (P : WeightedTorusHilbert.LogTorus n → Prop) :
    (∀ᵐ z ∂(WeightedTorusHilbert.weightedTorusMeasure k φ), P z) ↔
      ∀ᵐ z ∂(unweightedTorusMeasure n), P z := by
  rw [weightedTorusMeasure_eq_unweighted_withDensity hφ]
  have hd : Measurable
      (fun z : WeightedTorusHilbert.LogTorus n =>
        WeightedTorusHilbert.radialWeight k φ z.1) :=
    (WeightedTorusHilbert.radialWeight_measurable k hφ).comp
      measurable_fst
  rw [ae_withDensity_iff hd]
  constructor
  · intro h
    filter_upwards [h] with z hz
    exact hz (radialWeight_pos φ z.1).ne'
  · intro h
    filter_upwards [h] with z hz _
    exact hz
end Ehrhart.WeightedTorusGraphWeakBridge
