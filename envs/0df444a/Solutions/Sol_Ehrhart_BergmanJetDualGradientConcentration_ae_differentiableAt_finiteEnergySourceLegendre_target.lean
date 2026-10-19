-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientConcentration.ae_differentiableAt_finiteEnergySourceLegendre_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/26b858cc-533c-41b7-ae69-fce98861a084

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MomentRegularity_normalizedTargetBodyMeasure_eq_interior_restrict
import Theorems.Thm_Ehrhart_BergmanJetDualGradientConcentration_ae_differentiableAt_finiteEnergySourceLegendre_interior_restrict

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
    ∀ᵐ u : Space n ∂(normalizedTargetBodyMeasure K),
      DifferentiableAt ℝ (legendreTransform F.potential) u := by
  rw [normalizedTargetBodyMeasure_eq_interior_restrict K]
  exact Measure.ae_smul_measure
    (ae_differentiableAt_finiteEnergySourceLegendre_interior_restrict
      F htransport)
    (((volume : Measure (Space n)) K.carrier)⁻¹)
end Ehrhart.BergmanJetDualGradientConcentration
