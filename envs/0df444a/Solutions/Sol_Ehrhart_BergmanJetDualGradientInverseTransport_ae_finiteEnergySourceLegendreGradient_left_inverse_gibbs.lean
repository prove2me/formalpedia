-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientInverseTransport.ae_finiteEnergySourceLegendreGradient_left_inverse_gibbs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/0d75bc8c-67fb-4081-bd4e-3744807bcd2f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_ae_finiteEnergySourceGradient_mem_interior_gibbs
import Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_finiteEnergySourceLegendre_target
import Theorems.Thm_Ehrhart_BergmanJetDualPhaseConcentration_finiteEnergySourceLegendre_gradient_eq_phaseMaximizer

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
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F),
      SpatialBergmanFatouScheffe.actualGradient
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) = x := by
  have hsource :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) x :=
    finiteEnergySourceGibbs_ae_of_volume F _
      (ae_differentiableAt_finiteEnergySource F)
  have htarget :
      ∀ᵐ u : Space n
        ∂(finiteEnergySourceGradientPushforward F),
        DifferentiableAt ℝ (legendreTransform F.potential) u := by
    rw [htransport]
    exact ae_differentiableAt_finiteEnergySourceLegendre_target
      F htransport
  unfold finiteEnergySourceGradientPushforward at htarget
  have hdual :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        DifferentiableAt ℝ
          (legendreTransform F.potential)
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) :=
    MeasureTheory.ae_of_ae_map
      (measurable_finiteEnergySourceGradient F).aemeasurable
      htarget
  filter_upwards [hsource,
    ae_finiteEnergySourceGradient_mem_interior_gibbs F htransport,
    hdual] with x hx hinterior hdx
  exact finiteEnergySourceLegendre_gradient_eq_phaseMaximizer
    F htransport hinterior hdx x
      (fun z => finiteEnergySourcePhase_actualGradient_le F x hx z)
end Ehrhart.BergmanJetDualGradientInverseTransport
