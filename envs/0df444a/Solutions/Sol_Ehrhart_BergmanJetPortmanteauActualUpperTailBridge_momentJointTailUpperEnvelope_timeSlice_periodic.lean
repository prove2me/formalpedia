-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualUpperTailBridge.momentJointTailUpperEnvelope_timeSlice_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.11006+00:00
-- url     : https://prove2.me/submissions/13549f2f-4ade-433a-b4d6-27026134b9a0

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_EnvelopeSpatialPeriodicity_sourcePositiveJointTimePoint_spatial_translate
import Theorems.Thm_Ehrhart_BergmanJetSpatialPeriodicity_momentJointTailUpperEnvelope_spatial_invariant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge JetEnvelopeRightDerivative EnvelopeSpatialPeriodicity
open MomentOptimizer MomentTargetGeodesic MomentFirstVariation BergmanJetUpperEnvelope
open BergmanJetSpatialPeriodicity BergmanJetPortmanteauSlopeBridge
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (t : ℝ) (ht : 0 < t)
    (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointTailUpperEnvelope K F htransport p r
          (sourcePositiveJointTimePoint z t ht))
      (imaginaryShift m) := by
  intro z
  change
    momentJointTailUpperEnvelope K F htransport p r
      (sourcePositiveJointTimePoint (z + imaginaryShift m) t ht) =
    momentJointTailUpperEnvelope K F htransport p r
      (sourcePositiveJointTimePoint z t ht)
  rw [sourcePositiveJointTimePoint_spatial_translate]
  exact momentJointTailUpperEnvelope_spatial_invariant
    K F htransport p r m (sourcePositiveJointTimePoint z t ht)
end Ehrhart.BergmanJetPortmanteauActualUpperTailBridge
