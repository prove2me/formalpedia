-- Prove2me | solution 1 for Ehrhart.WeightedTorusDolbeault.continuous_angularCoverPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.693587+00:00
-- url     : https://prove2.me/submissions/ad80e442-9356-48b4-b7f9-ac0807161bd4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedTorusDolbeault
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.WeightedTorusDolbeault
theorem _root_.solution {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    Continuous (angularCoverPotential a) :=
  ha.comp (continuous_complexTorusCoverProjection n)
end Ehrhart.WeightedTorusDolbeault
