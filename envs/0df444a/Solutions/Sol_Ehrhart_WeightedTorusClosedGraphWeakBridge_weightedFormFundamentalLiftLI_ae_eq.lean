-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedFormFundamentalLiftLI_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/4e547f1d-e1f7-4b4d-8bf5-75e9230deea4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusClosedGraphWeakBridge
open Set Function MeasureTheory Filter
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
  Manifold ContDiff
namespace Ehrhart.WeightedTorusClosedGraphWeakBridge
theorem _root_.solution {n k : ℕ}
    (φ : Space n → ℝ) (b : Space n)
    (f : weightedTorusFormL2 k φ) :
    (fun p : Space n × Space n =>
      weightedFormFundamentalLiftLI k φ b f p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realWeightedFundamentalCell_measurePreserving φ b)
end Ehrhart.WeightedTorusClosedGraphWeakBridge
