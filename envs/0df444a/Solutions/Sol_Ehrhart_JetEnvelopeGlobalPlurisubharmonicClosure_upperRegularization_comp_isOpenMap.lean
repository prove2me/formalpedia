-- Prove2me | solution 1 for Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure.upperRegularization_comp_isOpenMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/1b0f908a-38c5-4ad9-8cb6-5dc0d0045342

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
open Set Filter Function MeasureTheory Metric
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope ActualJetPlurisubharmonicClosure
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace
namespace Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
theorem _root_.solution
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) (g : X → Y)
    (hg : Continuous g) (ho : IsOpenMap g) (x : X) :
    upperRegularization (fun y : X => f (g y)) x =
      upperRegularization f (g x) := by
  unfold upperRegularization
  congr 1
  ext c
  change
    (∀ᶠ y : X in 𝓝 x, f (g y) ≤ c) ↔
      ∀ᶠ z : Y in 𝓝 (g x), f z ≤ c
  rw [← ho.map_nhds_eq hg.continuousAt, Filter.eventually_map]
end Ehrhart.JetEnvelopeGlobalPlurisubharmonicClosure
