-- Prove2me | solution 1 for Ehrhart.BergmanJetDualGradientInverseTransport.measurable_finiteEnergySourceLegendreGradient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:25.658478+00:00
-- url     : https://prove2.me/submissions/97d1512a-9638-4d53-847b-a4de52dc940d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    (F : SourceFiniteEnergyPotential K) :
    Measurable
      (SpatialBergmanFatouScheffe.actualGradient
        (legendreTransform F.potential)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_fderiv_apply_const ℝ
    (legendreTransform F.potential)
    (Pi.single i (1 : ℝ))
end Ehrhart.BergmanJetDualGradientInverseTransport
