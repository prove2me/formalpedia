-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.tendsto_integral_momentBodyClampedTailPositiveSecant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/2cdbfa62-cbc9-41bc-a829-4ab8608cb684

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeGibbsBridge_ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_upperSemicontinuous_momentBodyClampedTailPositiveSecant
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyClampedTailPositiveSecant_nonneg
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_momentBodyClampedTailPositiveSecant_le_scale_add_inv
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_tendsto_momentBodyClampedTailPositiveSecant

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetPortmanteauActualVolumeBridge
open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative LogPartitionConvexity
open MomentRegularity BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetTorusEnvelope
open BergmanJetPartitionEndpoint BergmanJetTorusSlopeBridge BergmanJetTorusRightSlopeBridge
open BergmanJetTorusRightSlopeGibbsBridge BergmanJetBodyExponentialSecantBridge
open BergmanJetPortmanteauMovingUpperTailBridge BergmanJetPortmanteauActualUpperTailBridge
open BergmanJetTorusSlopeJointNeighborhoodUpper
open scoped BigOperators ENNReal NNReal Topology
namespace Ehrhart.BergmanJetPortmanteauActualVolumeBridge
theorem _root_.solution
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (ht : 0 < t) :
    Tendsto
      (fun r : ℕ =>
        ∫ q : LogTorus n,
          momentBodyClampedTailPositiveSecant K p r t ht q
            ∂(sourceProbability (momentBodyTorusWeight K p) 0))
      atTop
      (𝓝 (∫ q : LogTorus n,
        momentBodyEnvelopePositiveSecant K p t q
          ∂(sourceProbability (momentBodyTorusWeight K p) 0))) := by
  let μ : Measure (LogTorus n) :=
    sourceProbability (momentBodyTorusWeight K p) 0
  let : IsProbabilityMeasure μ :=
    sourceProbability_momentBody_isProbability K p 0
  have hlim :
      Tendsto
        (fun r : ℕ =>
          ∫ q : LogTorus n,
            momentBodyClampedTailPositiveSecant K p r t ht q ∂μ)
        atTop
        (𝓝 (∫ q : LogTorus n,
          max 0 (momentBodyEnvelopePositiveSecant K p t q) ∂μ)) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : LogTorus n => BodyScale.canonicalScale K + 1 / t)
    · intro r
      exact
        (upperSemicontinuous_momentBodyClampedTailPositiveSecant
          K p r t ht).measurable.aestronglyMeasurable
    · exact integrable_const _
    · intro r
      exact Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs,
          abs_of_nonneg
            (momentBodyClampedTailPositiveSecant_nonneg
              K p r t ht q)]
        exact momentBodyClampedTailPositiveSecant_le_scale_add_inv
          K p r t ht q
    · exact Filter.Eventually.of_forall
        (tendsto_momentBodyClampedTailPositiveSecant K p t ht)
  have hEq :
      (∫ q : LogTorus n,
        max 0 (momentBodyEnvelopePositiveSecant K p t q) ∂μ) =
        ∫ q : LogTorus n,
          momentBodyEnvelopePositiveSecant K p t q ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards
      [ae_momentBodyEnvelopePositiveSecant_nonneg_Gibbs K p ht]
      with q hq
    exact max_eq_right hq
  rw [hEq] at hlim
  exact hlim
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
