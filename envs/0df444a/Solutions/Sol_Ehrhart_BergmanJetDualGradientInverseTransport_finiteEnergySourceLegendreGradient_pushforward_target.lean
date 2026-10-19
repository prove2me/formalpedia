-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientInverseTransport.finiteEnergySourceLegendreGradient_pushforward_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/976d5393-f2e8-4e67-a6cb-d9cbbab7cdab

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_measurable_finiteEnergySourceLegendreGradient
import Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDualGradientInverseTransport
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentWeakFirstVariation MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetDualGradientConcentration
open BergmanJetDualPhaseConcentration
open scoped ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDualGradientInverseTransport
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Measure.map
        (SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential))
        (normalizedTargetBodyMeasure K) =
      finiteEnergySourceGibbsProbability F := by
  let G : Space n → Space n :=
    SpatialBergmanFatouScheffe.actualGradient F.potential
  let D : Space n → Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      (legendreTransform F.potential)
  have hG : Measurable G :=
    measurable_finiteEnergySourceGradient F
  have hD : Measurable D :=
    measurable_finiteEnergySourceLegendreGradient F
  have hleft :
      (D ∘ G) =ᵐ[finiteEnergySourceGibbsProbability F]
        (fun x : Space n => x) := by
    filter_upwards
      [ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
        F htransport] with x hx
    change
      SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) = x
    exact hx
  change Measure.map D (normalizedTargetBodyMeasure K) =
    finiteEnergySourceGibbsProbability F
  calc
    Measure.map D (normalizedTargetBodyMeasure K) =
        Measure.map D (finiteEnergySourceGradientPushforward F) := by
      rw [htransport]
    _ = Measure.map (D ∘ G)
          (finiteEnergySourceGibbsProbability F) := by
      unfold finiteEnergySourceGradientPushforward
      exact Measure.map_map hD hG
    _ = Measure.map (fun x : Space n => x)
          (finiteEnergySourceGibbsProbability F) :=
      Measure.map_congr hleft
    _ = finiteEnergySourceGibbsProbability F := Measure.map_id'
end Ehrhart.BergmanJetDualGradientInverseTransport
