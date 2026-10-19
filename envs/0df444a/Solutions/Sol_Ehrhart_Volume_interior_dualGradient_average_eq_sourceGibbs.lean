-- Prove2me | solution 1 for Ehrhart.Volume.interior_dualGradient_average_eq_sourceGibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:26.272914+00:00
-- url     : https://prove2.me/submissions/b120ed26-632e-4203-8789-4013732af2a7

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_integral_finiteEnergySourceLegendreGradient_target

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.Volume
open Set Function Filter MeasureTheory
open TorusCharacters LatticeAsymptotics BergmanMonomials BergmanNormalization LaplaceAsymptotics
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity BergmanJetPartitionEndpoint BergmanJetTriangularLatticeConvergence
open BergmanJetDiagonalObservableLatticeIdentity BergmanJetDualGradientInverseTransport
open BergmanJetUpperTaggedMonomialObservableConvergence BergmanJetPortmanteauActualVolumeBridge
open BergmanJetRadialHaarWeakProbabilityLift
open scoped BigOperators ENNReal NNReal Topology BoundedContinuousFunction
namespace Ehrhart.Volume
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f) :
    (∫ u in interior K.carrier,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
      ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) := by
  have hinterior :
      (∫ u in interior K.carrier,
        f (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u)
        ∂(volume : Measure (Space n))) =
        ∫ u in K.carrier,
          f (SpatialBergmanFatouScheffe.actualGradient
            (legendreTransform F.potential) u)
          ∂(volume : Measure (Space n)) :=
    MeasureTheory.setIntegral_congr_set
      (interior_ae_eq_of_null_frontier
        (K.convex.addHaar_frontier
          (volume : Measure (Space n))))
  rw [hinterior]
  calc
    (∫ u in K.carrier,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(volume : Measure (Space n))) /
        normalizedVolume K.carrier =
      ∫ u : Space n,
        f (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential) u)
        ∂(normalizedTargetBodyMeasure K) := by
      rw [integral_normalizedTargetBodyMeasure]
      ring
    _ = ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) :=
      integral_finiteEnergySourceLegendreGradient_target
        F htransport f hf
end Ehrhart.Volume
