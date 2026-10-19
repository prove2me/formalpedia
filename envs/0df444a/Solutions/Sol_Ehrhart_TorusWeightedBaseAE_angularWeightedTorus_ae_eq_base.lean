-- Prove2me | solution 1 for Ehrhart.TorusWeightedBaseAE.angularWeightedTorus_ae_eq_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/3a3957d7-77eb-42c5-9328-f9021520f560

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeightedBaseAE_angularWeightedTorus_ae_iff_base

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
    {n : ℕ} {E : Type*}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {f g : LogTorus n → E}
    (h : f =ᵐ[angularWeightedTorusMeasure a] g) :
    f =ᵐ[sourceTorusBaseMeasure n] g :=
  (angularWeightedTorus_ae_iff_base ha
    (fun p : LogTorus n => f p = g p)).mp h
end Ehrhart.TorusWeightedBaseAE
