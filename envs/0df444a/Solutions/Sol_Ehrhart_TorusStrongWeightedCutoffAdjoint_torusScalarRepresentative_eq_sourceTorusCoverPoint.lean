-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedCutoffAdjoint.torusScalarRepresentative_eq_sourceTorusCoverPoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/4f858bb4-9f47-4181-ad56-c5407780f6ff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongWeightedCutoffAdjoint
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongWeightedCutoffAdjoint
theorem _root_.solution
    {n : ℕ} (F : LogSpace n → ℂ) (q : LogTorus n) :
    torusScalarRepresentative F q = F (sourceTorusCoverPoint q) := by
  rfl
end Ehrhart.TorusStrongWeightedCutoffAdjoint
