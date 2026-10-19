-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentJointTailSup_local_le_maximum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/be349904-56d1-4c37-ab26-dc77e543bfe8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_eventually_momentPositiveJointGeodesic_local_le_maximum_add

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
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentJointTailSup K F htransport p r w ≤
        momentLocalPotentialMaximum K F p R + ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_local_le_maximum_add
      K F htransport p R hR hε)
  filter_upwards [eventually_ge_atTop N] with r hr w hw
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact hN (momentJointTailStart K F htransport p + r + j)
    (by omega) w hw
end Ehrhart.BergmanJetLocalEnvelopeGrowth
