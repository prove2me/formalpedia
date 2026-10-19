-- Prove2me | solution 1 for Ehrhart.MatrixTorusCompactGreen.angularWeight_mul_inverseAngularCoverWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/2cd241d8-77bd-41da-9d55-9207eb7980c7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusCompactGreen
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff
namespace Ehrhart.MatrixTorusCompactGreen
theorem _root_.solution {n : ℕ}
    (a : LogTorus n → ℝ)
    (p : Space n × Space n) :
    ((ENNReal.ofReal
      (angularWeightedTorusDensity a
        (realTorusCoverProjection n p))).toReal : ℂ) *
      inverseAngularCoverWeight a p = 1 := by
  simp only [angularWeightedTorusDensity,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    inverseAngularCoverWeight]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp
end Ehrhart.MatrixTorusCompactGreen
