-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedCutoffAdjoint.angularClosedMollifiedRadialAdjointCommutator_sub_weak
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/00593309-ca45-4eaa-a5ed-4842f0322344

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
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ) q -
      angularWeakSourceCutoffAdjointCommutator W m q =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (sourceCutoffBarGradient m q)
        (torusFormRepresentative
          (angularGraphMollifiedPhysicalField W ℓ) q - W q) := by
  unfold angularSourceCutoffAdjointCommutator
    angularWeakSourceCutoffAdjointCommutator
  rw [inner_sub_right]
end Ehrhart.TorusStrongWeightedCutoffAdjoint
