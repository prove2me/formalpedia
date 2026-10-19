-- Prove2me | solution 1 for Ehrhart.BergmanJetPartitionEndpoint.momentBodyLogPartition_eq_sourceLogPartition_add_log_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/841c75a6-02ae-43de-9498-85b6154730a8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPartitionEndpoint
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentTargetDanskin
open MomentFirstVariation MomentRegularity BergmanJetTorusEnvelope BergmanJetTorusCoercivity
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetPartitionEndpoint
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    momentBodyLogPartition K p t =
      sourceLogPartition (momentBodyTorusWeight K p) t +
        Real.log (normalizedVolume K.carrier) := by
  change
    -Real.log
      (momentBodyPartition K p t /
        normalizedVolume K.carrier) =
      -Real.log (momentBodyPartition K p t) +
        Real.log (normalizedVolume K.carrier)
  rw [Real.log_div
    (momentBodyPartition_pos K p t).ne'
    K.volume_pos.ne']
  ring
end Ehrhart.BergmanJetPartitionEndpoint
