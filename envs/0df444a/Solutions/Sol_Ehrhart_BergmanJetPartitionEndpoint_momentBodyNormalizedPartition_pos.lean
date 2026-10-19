-- Prove2me | solution 1 for Ehrhart.BergmanJetPartitionEndpoint.momentBodyNormalizedPartition_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/f3417768-7e8b-43e1-bb48-b6dcc8824669

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
    0 < momentBodyNormalizedPartition K p t := by
  exact div_pos (momentBodyPartition_pos K p t) K.volume_pos
end Ehrhart.BergmanJetPartitionEndpoint
