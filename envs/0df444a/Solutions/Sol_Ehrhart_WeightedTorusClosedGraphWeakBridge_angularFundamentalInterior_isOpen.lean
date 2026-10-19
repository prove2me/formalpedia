-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.angularFundamentalInterior_isOpen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/044ad2ab-02e7-46dc-9663-0fad8f1ecf22

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
    (b : Space n) :
    IsOpen (angularFundamentalInterior b) := by
  simpa [angularFundamentalInterior, Set.pi] using
    (isOpen_set_pi (s := fun i : Fin n => Set.Ioo (b i) (b i + 1))
      Set.finite_univ (fun _ _ => isOpen_Ioo))
end Ehrhart.WeightedTorusClosedGraphWeakBridge
