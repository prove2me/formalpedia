-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_finiteEnergySourceLegendre_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/20ccfb36-6aae-4c38-8439-4d461061b312

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentInteriorLegendre_locallyLipschitzOn_finiteEnergySourceLegendre_interior
import Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_of_locallyLipschitzOn_open

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.BergmanJetDualGradientConcentration
open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentInteriorLegendre
open scoped ENNReal NNReal Topology
namespace Ehrhart.BergmanJetDualGradientConcentration
theorem _root_.solution
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᵐ u : Space n ∂(volume : Measure (Space n)),
      u ∈ interior K.carrier →
        DifferentiableAt ℝ (legendreTransform F.potential) u := by
  exact ae_differentiableAt_of_locallyLipschitzOn_open
    isOpen_interior
    (locallyLipschitzOn_finiteEnergySourceLegendre_interior
      F htransport)
end Ehrhart.BergmanJetDualGradientConcentration
