-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.coverTestWithinFundamentalCell_of_tsupport_subset_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/5a8650c0-7c92-45ac-9c4b-1cd69121881e

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
theorem _root_.solution
    {n : ℕ} (b : Space n)
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : tsupport ψ ⊆ coverFundamentalInterior b) :
    tsupport ψ ⊆ coverFundamentalCell b := by
  intro z hz
  have h := hψ hz
  intro i
  exact ⟨h i |>.1, (h i).2.le⟩
end Ehrhart.WeightedTorusClosedGraphWeakBridge
