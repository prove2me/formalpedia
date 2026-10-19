-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.coverTest_zero_outside_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/1247a339-ef8b-4a37-92bf-14d43fa913b0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverBarPartialTest_eq_zero_of_notMem_tsupport
import Theorems.Thm_Ehrhart_WeightedTorusClosedGraphWeakBridge_coverRealTest_eq_zero_of_notMem_tsupport

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
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (p : Space n × Space n)
    (hp : p.2 ∉ angularFundamentalBox b) :
    ψ (logarithmicCoordinatesEquiv n p) = 0 ∧
      ∀ j : Fin n,
        coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p) = 0 := by
  have hz : logarithmicCoordinatesEquiv n p ∉ tsupport ψ := by
    intro hz
    apply hp
    have hm :
        ((logarithmicCoordinatesEquiv n).symm
          (logarithmicCoordinatesEquiv n p)).2 ∈
            angularFundamentalBox b := hcell hz
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hm
  exact ⟨coverRealTest_eq_zero_of_notMem_tsupport hz,
    fun j => coverBarPartialTest_eq_zero_of_notMem_tsupport j hz⟩
end Ehrhart.WeightedTorusClosedGraphWeakBridge
