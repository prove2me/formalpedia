-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_finiteEnergySourceLegendre_interior_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/cd5e70e9-050e-4ebc-9340-354563174cc6

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_finiteEnergySourceLegendre_interior

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
    ∀ᵐ u : Space n
      ∂((volume : Measure (Space n)).restrict
        (interior K.carrier)),
      DifferentiableAt ℝ (legendreTransform F.potential) u := by
  exact (ae_restrict_iff' isOpen_interior.measurableSet).2
    (ae_differentiableAt_finiteEnergySourceLegendre_interior
      F htransport)
end Ehrhart.BergmanJetDualGradientConcentration
