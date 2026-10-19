-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.momentEnvelopeTimeSlice_local_le_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/65070ad3-b0e7-4718-98a0-b52c06cb8cff

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_momentJointUpperEnvelope_local_le_maximum

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
    (p z : LogSpace n) (R t : ℝ) (hR : 0 < R) (ht : 0 < t)
    (hz : dist z p < R * Real.exp (-t / 2)) :
    momentEnvelopeTimeSlice K F htransport p z t ≤
      momentLocalPotentialMaximum K F p R := by
  rw [momentEnvelopeTimeSlice, dif_pos ht]
  apply momentJointUpperEnvelope_local_le_maximum
    K F htransport p R hR
  change dist z p <
    R * Real.exp
      (-jointLogTime (sourcePositiveJointTimePoint z t ht) / 2)
  simpa [jointLogTime_sourcePositiveJointTimePoint] using hz
end Ehrhart.BergmanJetLocalEnvelopeGrowth
