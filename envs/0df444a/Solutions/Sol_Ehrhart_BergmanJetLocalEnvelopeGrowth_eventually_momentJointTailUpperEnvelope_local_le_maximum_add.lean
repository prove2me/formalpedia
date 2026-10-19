-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentJointTailUpperEnvelope_local_le_maximum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/b604a00a-162a-4cb7-aef7-48e2b8af8a6e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_isOpen_sourceLocalJointRegion
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_eventually_momentJointTailSup_local_le_maximum_add

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
      momentJointTailUpperEnvelope K F htransport p r w ≤
        momentLocalPotentialMaximum K F p R + ε := by
  filter_upwards
    [eventually_momentJointTailSup_local_le_maximum_add
      K F htransport p R hR hε]
    with r hr w hw
  unfold momentJointTailUpperEnvelope
  apply upperRegularization_le_of_eventually
  exact Filter.mem_of_superset
    ((isOpen_sourceLocalJointRegion p R).mem_nhds hw)
    (fun v hv => hr v hv)
end Ehrhart.BergmanJetLocalEnvelopeGrowth
