-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedTorusDescent.torusScalarRepresentative_realTorusCoverProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/f6ba4bec-46ba-40b3-a80e-8168361273d5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_coverRepresentative_coe

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
    {n : ℕ} (F : LogSpace n → ℂ)
    (p : Space n × Space n)
    (hbox : p.2 ∈ angularFundamentalBox (0 : Space n)) :
    torusScalarRepresentative F (realTorusCoverProjection n p) =
      F (logarithmicPoint p.1 p.2) := by
  apply coverRepresentative_coe
  intro i _
  simpa [angularFundamentalBox] using hbox i
end Ehrhart.TorusStrongWeightedTorusDescent
