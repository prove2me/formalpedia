-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.momentJointUpperEnvelope_local_le_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/527b4939-1f2a-4592-9563-d1469867a618

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_eventually_momentJointTailUpperEnvelope_local_le_maximum_add

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetLocalEnvelopeGrowth
open Set Function Filter MeasureTheory Module Metric
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentFirstVariation MomentTargetGeodesic
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetLocalGrowth ActualJetUpperEnvelope
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative JetEnvelopeLocalGrowth
open LogPartitionConvexity
open scoped BigOperators ENNReal Topology
namespace Ehrhart.BergmanJetLocalEnvelopeGrowth
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (R : ℝ) (hR : 0 < R)
    (w : PositiveJointLogSpace n)
    (hw : w ∈ sourceLocalJointRegion p R) :
    momentJointUpperEnvelope K F htransport p w ≤
      momentLocalPotentialMaximum K F p R := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr⟩ :=
    (eventually_momentJointTailUpperEnvelope_local_le_maximum_add
      K F htransport p R hR hε).exists
  calc
    momentJointUpperEnvelope K F htransport p w ≤
      momentJointTailUpperEnvelope K F htransport p r w :=
        ciInf_le (momentJointTailUpperEnvelope_bddBelow
          K F htransport p w) r
    _ ≤ momentLocalPotentialMaximum K F p R + ε := hr w hw
end Ehrhart.BergmanJetLocalEnvelopeGrowth
