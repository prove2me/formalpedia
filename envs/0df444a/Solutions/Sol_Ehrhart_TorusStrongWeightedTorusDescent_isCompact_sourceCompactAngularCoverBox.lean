-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedTorusDescent.isCompact_sourceCompactAngularCoverBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/be458166-4f5c-450c-b55e-1345d650ad4e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusStrongWeightedTorusDescent
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusStrongWeightedTorusDescent
theorem _root_.solution
    {n : ℕ} {S : Set (LogTorus n)} (hS : IsCompact S) :
    IsCompact (sourceCompactAngularCoverBox S) := by
  unfold sourceCompactAngularCoverBox
  exact ((hS.image continuous_fst).prod
    (isCompact_univ_pi fun _ : Fin n => isCompact_Icc)).image
      (logarithmicCoordinatesEquiv n).continuous
end Ehrhart.TorusStrongWeightedTorusDescent
