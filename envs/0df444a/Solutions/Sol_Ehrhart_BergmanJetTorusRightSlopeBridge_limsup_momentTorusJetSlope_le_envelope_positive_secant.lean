-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.limsup_momentTorusJetSlope_le_envelope_positive_secant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/50ec7860-443a-4fa1-9894-c05511245307

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetEnvelopeLimit_tendsto_momentJointTailUpperEnvelope
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_limsup_momentTorusJetSlope_le_tail_positive_secant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetTorusRightSlopeBridge
open Set Function Filter MeasureTheory Metric
open TorusCharacters WeightedTorusHilbert SupportFunction LaplaceAsymptotics BergmanMonomials
open BergmanGeodesicConvexity JetEnvelopeRightDerivative ActualJetUpperEnvelope MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakGlobalKernel
open BergmanJetGeodesic BergmanJetProfileBridge BergmanJetRealGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopeLimit BergmanJetTorusEnvelope BergmanJetTorusSlopeBridge
open BergmanJetPointwiseLogKernel
open scoped BigOperators ENNReal InnerProductSpace Topology
namespace Ehrhart.BergmanJetTorusRightSlopeBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    {u : Space n} (hu : u ∈ interior K.carrier)
    (hmax : ∀ x : Space n,
      phase u (momentNormalizedPotential F) x ≤
        phase u (momentNormalizedPotential F) q.1)
    {t : ℝ} (ht : 0 < t) :
    Filter.limsup
        (fun k : ℕ =>
          momentTorusJetSlope K F htransport p k q) atTop ≤
      (momentTorusEnvelopeTimeSlice
          K F htransport p q t -
        momentTorusEnvelopeTimeSlice
          K F htransport p q 0) / t := by
  let z := sourceTorusCoverPoint q
  let w := sourcePositiveJointTimePoint z t ht
  have htail :=
    tendsto_momentJointTailUpperEnvelope
      K F htransport p w
  have hquot :
      Tendsto
        (fun r : ℕ =>
          (momentJointTailUpperEnvelope
            K F htransport p r w -
              momentNormalizedPotential F q.1) / t)
        atTop
        (𝓝 ((momentJointUpperEnvelope
          K F htransport p w -
            momentNormalizedPotential F q.1) / t)) :=
    (htail.sub_const
      (momentNormalizedPotential F q.1)).div_const t
  have hle :
      Filter.limsup
          (fun k : ℕ =>
            momentTorusJetSlope K F htransport p k q) atTop ≤
        (momentJointUpperEnvelope
          K F htransport p w -
            momentNormalizedPotential F q.1) / t := by
    apply ge_of_tendsto hquot
    exact Filter.Eventually.of_forall fun r =>
      limsup_momentTorusJetSlope_le_tail_positive_secant
        K F htransport p q hu hmax r ht
  simpa [momentTorusEnvelopeTimeSlice,
    momentEnvelopeTimeSlice, ht, z, w,
    realLogCoordinate_sourceTorusCoverPoint] using hle
end Ehrhart.BergmanJetTorusRightSlopeBridge
