-- Prove2me | solution 1 for Ehrhart.WeightedTorusWeylRadialIntegrationBridge.compactPolarDomain_subset_polarTarget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.88399+00:00
-- url     : https://prove2.me/submissions/4d63611d-24a6-427e-97d2-3608898c9ff0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusWeylRadialIntegrationBridge
open Set MeasureTheory Filter Complex
open scoped BigOperators ContDiff Convolution ENNReal Topology
open WeightedTorusWeylRepresentativeBridge
namespace Ehrhart.WeightedTorusWeylRadialIntegrationBridge
theorem _root_.solution :
    compactPolarDomain ⊆ Complex.polarCoord.target := by
  rw [Complex.polarCoord_target]
  intro p hp
  exact ⟨hp.1.1, hp.2⟩
end Ehrhart.WeightedTorusWeylRadialIntegrationBridge
