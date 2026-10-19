-- Prove2me | solution 1 for Ehrhart.BergmanJetPortmanteauActualVolumeBridge.momentBodySharpJetScale_le_dimension_of_weakProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/8cb2a0a5-df69-4a6f-80b7-ef6a5758bdad

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetBodyExponentialSecantBridge_integral_momentBodyEnvelopePositiveSecant_le_dimension_mul_exp
import Theorems.Thm_Ehrhart_BergmanJetPortmanteauActualVolumeBridge_integral_momentBodyEnvelopePositiveSecant_ge_sharp_of_weak

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
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (hweak : Tendsto (momentBodyMovingBergmanProbability K) atTop
      (𝓝 (momentBodyZeroGibbsProbability K (0 : LogSpace n)))) :
    (n : ℝ) * BodyScale.canonicalScale K /
      ((n : ℝ) + 1) ≤ (n : ℝ) := by
  have htend :
      Tendsto
        (fun k : ℕ => 1 / ((k : ℝ) + 1))
        atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          (n : ℝ) *
            Real.exp (BodyScale.canonicalScale K * t)) :=
    continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  have hlimit :
      Tendsto
        (fun k : ℕ =>
          (n : ℝ) * Real.exp
            (BodyScale.canonicalScale K *
              (1 / ((k : ℝ) + 1))))
        atTop (𝓝 (n : ℝ)) := by
    have h := hcontinuous.continuousAt.tendsto.comp htend
    have hzero :
        (n : ℝ) *
            Real.exp (BodyScale.canonicalScale K * 0) =
          (n : ℝ) := by
      simp
    rw [hzero] at h
    refine h.congr' (Filter.Eventually.of_forall fun k => ?_)
    rfl
  apply ge_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun k => by
    have ht : 0 < (1 / ((k : ℝ) + 1)) := by positivity
    calc
      (n : ℝ) * BodyScale.canonicalScale K /
        ((n : ℝ) + 1) ≤
          ∫ q : LogTorus n,
            momentBodyEnvelopePositiveSecant
              K (0 : LogSpace n) (1 / ((k : ℝ) + 1)) q
              ∂(sourceProbability
                (momentBodyTorusWeight K (0 : LogSpace n)) 0) :=
        integral_momentBodyEnvelopePositiveSecant_ge_sharp_of_weak
          hn K (0 : LogSpace n) hweak ht
      _ ≤ (n : ℝ) * Real.exp
          (BodyScale.canonicalScale K *
            (1 / ((k : ℝ) + 1))) :=
        integral_momentBodyEnvelopePositiveSecant_le_dimension_mul_exp
          K ht
end Ehrhart.BergmanJetPortmanteauActualVolumeBridge
