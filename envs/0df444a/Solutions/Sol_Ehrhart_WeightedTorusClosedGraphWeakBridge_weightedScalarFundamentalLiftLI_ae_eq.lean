-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.weightedScalarFundamentalLiftLI_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/8a5b4ca0-3d6d-467f-ad42-accb071caaac

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
    (f : weightedTorusScalarL2 k φ) :
    (fun p : Space n × Space n =>
      weightedScalarFundamentalLiftLI k φ b f p) =ᵐ[
        realWeightedFundamentalCellMeasure k φ b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realWeightedFundamentalCell_measurePreserving φ b)
end Ehrhart.WeightedTorusClosedGraphWeakBridge
