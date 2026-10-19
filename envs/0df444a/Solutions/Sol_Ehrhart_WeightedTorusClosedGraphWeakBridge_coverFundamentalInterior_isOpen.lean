-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.coverFundamentalInterior_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/20dedfbf-2bd6-4c19-b50f-7ae02c005d51

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_angularFundamentalInterior_isOpen

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
    (b : Space n) :
    IsOpen (coverFundamentalInterior b) := by
  exact (angularFundamentalInterior_isOpen b).preimage
    (continuous_snd.comp (logarithmicCoordinatesEquiv n).symm.continuous)
end Ehrhart.WeightedTorusClosedGraphWeakBridge
