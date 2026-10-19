-- Prove2me | solution 1 for Ehrhart.BergmanJetLocalEnvelopeGrowth.eventually_momentPositiveJointGeodesic_local_le_maximum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/6798405c-d13c-4531-b5a3-80de22107d94

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JetEnvelopeLocalGrowth_tendsto_sourceLocalKernelLogError
import Theorems.Thm_Ehrhart_BergmanJetLocalEnvelopeGrowth_eventually_momentPositiveJointGeodesic_local_bound

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
    ∀ᶠ k : ℕ in atTop, ∀ w ∈ sourceLocalJointRegion p R,
      momentPositiveJointGeodesic K F htransport p k w ≤
        momentLocalPotentialMaximum K F p R + ε := by
  have herr : ∀ᶠ k : ℕ in atTop,
      sourceLocalKernelLogError K (k + 1) < ε := by
    have htend := (tendsto_sourceLocalKernelLogError K).comp
      (Filter.tendsto_add_atTop_nat 1)
    exact htend (Iio_mem_nhds hε)
  filter_upwards
    [eventually_momentPositiveJointGeodesic_local_bound
      K F htransport p R hR, herr]
    with k hbound hsmall w hw
  exact (hbound w hw).trans (by linarith)
end Ehrhart.BergmanJetLocalEnvelopeGrowth
