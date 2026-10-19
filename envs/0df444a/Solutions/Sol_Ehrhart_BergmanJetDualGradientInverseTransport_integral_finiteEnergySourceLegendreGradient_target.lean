-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientInverseTransport.integral_finiteEnergySourceLegendreGradient_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/8c0e5500-8963-4b24-9b1e-e1e3aa8aab7a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_measurable_finiteEnergySourceLegendreGradient
import Theorems.Thm_Ehrhart_BergmanJetDualGradientInverseTransport_finiteEnergySourceLegendreGradient_pushforward_target

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
      normalizedTargetBodyMeasure K)
    (f : Space n → ℝ)
    (hf : Continuous f) :
    (∫ u : Space n,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(normalizedTargetBodyMeasure K)) =
      ∫ x : Space n, f x
        ∂(finiteEnergySourceGibbsProbability F) := by
  calc
    (∫ u : Space n,
      f (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential) u)
      ∂(normalizedTargetBodyMeasure K)) =
        ∫ x : Space n, f x
          ∂(Measure.map
            (SpatialBergmanFatouScheffe.actualGradient
              (legendreTransform F.potential))
            (normalizedTargetBodyMeasure K)) := by
      symm
      exact MeasureTheory.integral_map
        (measurable_finiteEnergySourceLegendreGradient F).aemeasurable
        hf.aestronglyMeasurable
    _ = ∫ x : Space n, f x
          ∂(finiteEnergySourceGibbsProbability F) := by
      rw [finiteEnergySourceLegendreGradient_pushforward_target
        F htransport]
end Ehrhart.BergmanJetDualGradientInverseTransport
