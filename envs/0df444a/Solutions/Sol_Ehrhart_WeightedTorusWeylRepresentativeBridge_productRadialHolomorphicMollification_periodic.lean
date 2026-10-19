-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRepresentativeBridge.productRadialHolomorphicMollification_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/45b00301-bd62-4d5e-97d6-3cd48c797cd4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRepresentativeBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open DolbeaultRegularity DolbeaultGraphDistributionBridge
namespace Ehrhart.WeightedTorusWeylRepresentativeBridge
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {d : TorusCharacters.LogSpace n}
    (hperiod : Function.Periodic g d) :
    Function.Periodic (productRadialHolomorphicMollification g) d := by
  unfold productRadialHolomorphicMollification
  rw [← complex_convolution_flip]
  exact complexReal_convolution_periodic
    (normalizedProductRadialKernel (n := n)) hperiod
end Ehrhart.WeightedTorusWeylRepresentativeBridge
