-- Prove2me | solution 1 for Ehrhart.WeightedTorusGraphWeakBridge.realTorusCoverLift_ae_eq_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/c00cd1fa-e417-4720-8629-2304ee1bf15c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ}
    {f g : WeightedTorusHilbert.LogTorus n → ℂ}
    (h : f =ᵐ[unweightedTorusMeasure n] g)
    (q : Fin n → ℤ) :
    realTorusCoverLift f =ᵐ[
      (volume : Measure (Space n × Space n)).restrict
        ((Set.univ : Set (Space n)) ×ˢ
          angularFundamentalBox (fun i => (q i : ℝ)))]
      realTorusCoverLift g := by
  have hp :=
    (realTorusCoverProjection_measurePreserving
      (volume : Measure (Space n))
      (fun i => (q i : ℝ))).quasiMeasurePreserving.ae_eq_comp h
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
  simp only [Measure.restrict_univ]
  filter_upwards [hp] with x hx
  change f (realTorusCoverProjection n x) =
    g (realTorusCoverProjection n x)
  exact hx
end Ehrhart.WeightedTorusGraphWeakBridge
