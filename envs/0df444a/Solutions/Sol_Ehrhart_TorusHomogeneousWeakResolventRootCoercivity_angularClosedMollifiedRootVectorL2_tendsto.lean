-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularClosedMollifiedRootVectorL2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/df0ec271-2403-4676-8a63-8f55286d382d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularGraphMollifiedPhysicalField_compact_weighted_L2_tendsto_zero
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularClosedMollifiedRootVectorL2_sub_norm_sq_le

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
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRootVectorL2 ha ha2 hH W ℓ m)
      atTop
      (nhds
        (angularPhysicalResolventRootCutoffL2 ha2 hH W m)) := by
  have hS := (sourceRadialCutoff_hasCompactSupport
    (n := n) m).isCompact
  obtain ⟨B, hBpos, hB⟩ :=
    exists_angularHessianSquareRoot_fiber_bound_on_compact
      ha2 hH hS
  have hlocal :=
    TorusHomogeneousCutoffAdjoint.angularGraphMollifiedPhysicalField_compact_weighted_L2_tendsto_zero
      ha W hS
  have hsq :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRootVectorL2
              ha ha2 hH W ℓ m -
            angularPhysicalResolventRootCutoffL2
              ha2 hH W m‖ ^ 2)
        atTop (nhds 0) := by
    apply squeeze_zero (fun ℓ => sq_nonneg _)
      (fun ℓ => angularClosedMollifiedRootVectorL2_sub_norm_sq_le
        ha ha2 hH W ℓ m hBpos.le hB)
    simpa using hlocal.const_mul (B ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa [Real.sqrt_sq_eq_abs] using hsq.sqrt
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
