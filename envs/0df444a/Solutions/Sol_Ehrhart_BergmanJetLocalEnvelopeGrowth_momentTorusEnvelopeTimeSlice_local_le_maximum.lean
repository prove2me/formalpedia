-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.momentTorusEnvelopeTimeSlice_local_le_maximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/8dc5805b-811b-4604-8a50-3697d6e5954c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_momentEnvelopeTimeSlice_local_le_maximum

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
    (p : LogSpace n) (q : LogTorus n)
    (R t : ℝ) (hR : 0 < R) (ht : 0 < t)
    (hq : dist (sourceTorusCoverPoint q) p <
      R * Real.exp (-t / 2)) :
    momentTorusEnvelopeTimeSlice K F htransport p q t ≤
      momentLocalPotentialMaximum K F p R := by
  exact momentEnvelopeTimeSlice_local_le_maximum
    K F htransport p (sourceTorusCoverPoint q) R t hR ht hq
end Ehrhart.BergmanJetLocalEnvelopeGrowth
