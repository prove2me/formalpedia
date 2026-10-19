-- Prove2me | solution 1 for Ehrhart.TorusStrongWeightedTorusDescent.logarithmicPoint_mem_sourceCompactAngularCoverBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/0facffe0-61d0-4024-a918-4970b8988a5d

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
    {n : ℕ} {S : Set (LogTorus n)}
    (p : Space n × Space n)
    (hbox : p.2 ∈ angularFundamentalBox (0 : Space n))
    (hS : realTorusCoverProjection n p ∈ S) :
    logarithmicPoint p.1 p.2 ∈ sourceCompactAngularCoverBox S := by
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨realTorusCoverProjection n p, hS, rfl⟩
  · intro i _
    have hi := hbox i
    exact ⟨hi.1.le, by simpa using hi.2⟩
  · simpa using logarithmicCoordinatesEquiv_apply p.1 p.2
end Ehrhart.TorusStrongWeightedTorusDescent
