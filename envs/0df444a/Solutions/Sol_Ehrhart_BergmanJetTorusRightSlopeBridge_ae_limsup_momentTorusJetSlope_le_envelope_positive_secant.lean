-- Prove2me | solution 1 for Ehrhart.BergmanJetTorusRightSlopeBridge.ae_limsup_momentTorusJetSlope_le_envelope_positive_secant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/beb81f02-963c-4a55-8f52-10f0b7e17f97

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_ae_finiteEnergySourceGradient_mem_interior_volume
import Theorems.Thm_Ehrhart_BergmanJetTorusRightSlopeBridge_limsup_momentTorusJetSlope_le_envelope_positive_secant

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
    (p : LogSpace n) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      ∀ θ : AngularTorus n,
        Filter.limsup
            (fun k : ℕ =>
              momentTorusJetSlope
                K F htransport p k (x, θ)) atTop ≤
          (momentTorusEnvelopeTimeSlice
              K F htransport p (x, θ) t -
            momentTorusEnvelopeTimeSlice
              K F htransport p (x, θ) 0) / t := by
  filter_upwards
    [ae_differentiableAt_finiteEnergySource F,
      ae_finiteEnergySourceGradient_mem_interior_volume
        F htransport] with x hx hinterior θ
  let u : Space n :=
    SpatialBergmanFatouScheffe.actualGradient F.potential x
  have hmax : ∀ z : Space n,
      phase u (momentNormalizedPotential F) z ≤
        phase u (momentNormalizedPotential F) x := by
    intro z
    have h := finiteEnergySourcePhase_actualGradient_le F x hx z
    change phase u F.potential z ≤ phase u F.potential x at h
    unfold phase at h ⊢
    change
      pairing u z -
          (F.potential z +
            Real.log
              (finiteEnergySourcePartition F /
                normalizedVolume K.carrier)) ≤
        pairing u x -
          (F.potential x +
            Real.log
              (finiteEnergySourcePartition F /
                normalizedVolume K.carrier))
    linarith
  exact limsup_momentTorusJetSlope_le_envelope_positive_secant
    K F htransport p (x, θ) hinterior hmax ht
end Ehrhart.BergmanJetTorusRightSlopeBridge
