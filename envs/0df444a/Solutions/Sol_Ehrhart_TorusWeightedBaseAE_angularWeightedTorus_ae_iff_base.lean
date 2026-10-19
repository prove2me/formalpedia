-- Prove2me | solution 1 for Ehrhart.TorusWeightedBaseAE.angularWeightedTorus_ae_iff_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/2973967e-fa93-4304-8040-595195a1fa7e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusDolbeault_angularWeightedTorusDensity_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedBaseAE
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusWeightedBaseAE
theorem _root_.solution
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (P : LogTorus n → Prop) :
    (∀ᵐ p ∂(angularWeightedTorusMeasure a), P p) ↔
      ∀ᵐ p ∂(sourceTorusBaseMeasure n), P p := by
  rw [angularWeightedTorusMeasure]
  have hd : Measurable
      (fun p : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a p)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  rw [ae_withDensity_iff hd]
  constructor
  · intro h
    filter_upwards [h] with p hp
    exact hp
      (ENNReal.ofReal_pos.mpr
        (angularWeightedTorusDensity_pos a p)).ne'
  · intro h
    filter_upwards [h] with p hp _
    exact hp
end Ehrhart.TorusWeightedBaseAE
