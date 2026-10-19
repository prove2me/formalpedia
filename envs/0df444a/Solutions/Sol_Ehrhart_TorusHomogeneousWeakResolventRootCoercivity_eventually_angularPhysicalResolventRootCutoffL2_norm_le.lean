-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.eventually_angularPhysicalResolventRootCutoffL2_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/72c8c27a-8cc7-4339-8a05-b5f76a15423a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_RadialPhysicalResolventRootCutoffUniformExtraction_sourceRadialCutoff_eventually_one_on_compact
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularPhysicalResolventRootCutoffL2_norm_le_of_one_on_support

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open JetEnvelopeRightDerivative EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerCoreDensity
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy TorusWeakRadialBochnerUpperBound
open TorusWeakRadialExteriorMollification TorusClosedMollifiedRootBochner
open TorusStrongWeightedCutoffAdjoint TorusWeakResolventRootBochner
open RadialPhysicalResolventRootCutoffUniformExtraction TorusHomogeneousSmoothRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff
namespace Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (m : ℕ) :
    ∀ᶠ M : ℕ in atTop,
      ‖angularPhysicalResolventRootCutoffL2 ha2 hH W m‖ ≤
        ‖angularPhysicalResolventRootCutoffL2 ha2 hH W M‖ := by
  filter_upwards
    [sourceRadialCutoff_eventually_one_on_compact
      (sourceRadialCutoff_hasCompactSupport m).isCompact]
    with M hM
  exact angularPhysicalResolventRootCutoffL2_norm_le_of_one_on_support
    ha2 hH W m M hM
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
