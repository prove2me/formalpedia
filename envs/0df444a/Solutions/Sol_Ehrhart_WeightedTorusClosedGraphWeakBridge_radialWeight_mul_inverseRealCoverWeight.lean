-- Prove2me | solution 1 for Ehrhart.WeightedTorusClosedGraphWeakBridge.radialWeight_mul_inverseRealCoverWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:15.229985+00:00
-- url     : https://prove2.me/submissions/839a40d6-10bb-46b3-9b9e-a12647e94ae4

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
    (φ : Space n → ℝ)
    (p : Space n × Space n) :
    ((radialWeight k φ p.1).toReal : ℂ) *
      inverseRealCoverWeight k φ p = 1 := by
  simp only [radialWeight, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    inverseRealCoverWeight]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have h : -(k : ℝ) * φ p.1 + (k : ℝ) * φ p.1 = 0 := by
    ring
  rw [h]
  simp
end Ehrhart.WeightedTorusClosedGraphWeakBridge
