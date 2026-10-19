-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.self_mem_coverFundamentalInterior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/6d6058b9-c319-4d2e-ac81-04e3114d05ec

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
theorem _root_.solution {n : ℕ}
    (z : TorusCharacters.LogSpace n) :
    z ∈ coverFundamentalInterior (coverCenteredFundamentalBase z) := by
  intro i
  change
    ((logarithmicCoordinatesEquiv n).symm z).2 i ∈
      Set.Ioo
        (((logarithmicCoordinatesEquiv n).symm z).2 i -
          (1 / 2 : ℝ))
        (((logarithmicCoordinatesEquiv n).symm z).2 i -
          (1 / 2 : ℝ) + 1)
  constructor <;> linarith
end Ehrhart.WeightedTorusClosedGraphWeakBridge
