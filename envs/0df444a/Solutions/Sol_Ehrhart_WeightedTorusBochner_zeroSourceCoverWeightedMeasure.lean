-- Prove2me | solution 1 for Ehrhart.WeightedTorusBochner.zeroSourceCoverWeightedMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/f7d85dbe-75eb-4eef-9c57-c1c3afb11336

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusBochner
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusBochner
theorem _root_.solution {n : ℕ} :
    coverWeightedMeasure
      (matrixSourceCoverPotential (fun _ : Space n => (0 : ℝ))) =
        (volume : Measure (TorusCharacters.LogSpace n)) := by
  simp [coverWeightedMeasure, coverWeight, matrixSourceCoverPotential]
end Ehrhart.WeightedTorusBochner
