-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularPhysicalResolventRootCutoffL2_norm_le_of_one_on_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/d8d334e8-0ea6-4bdb-beb1-46421f1cf15c

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreConvergence_complexLp_norm_le_of_ae_norm_le

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
    (m M : ℕ)
    (hone : ∀ q ∈ tsupport (sourceRadialCutoff (n := n) m),
      sourceRadialCutoff M q = 1) :
    ‖angularPhysicalResolventRootCutoffL2 ha2 hH W m‖ ≤
      ‖angularPhysicalResolventRootCutoffL2 ha2 hH W M‖ := by
  let hm := angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W m
  let hM := angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W M
  change
    ‖hm.toLp (angularPhysicalResolventRootCutoffField a W m)‖ ≤
      ‖hM.toLp (angularPhysicalResolventRootCutoffField a W M)‖
  have hcomp := complexLp_norm_le_of_ae_norm_le
    hm hM (C := (1 : ℝ)) zero_le_one
      (by
        filter_upwards [] with q
        by_cases hq :
            q ∈ tsupport (sourceRadialCutoff (n := n) m)
        · have hMq := hone q hq
          unfold angularPhysicalResolventRootCutoffField
          rw [hMq]
          simp only [Complex.ofReal_one, one_smul, one_mul,
            norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (sourceRadialCutoff_le_one m q)
        · have hmq : sourceRadialCutoff m q = 0 :=
            image_eq_zero_of_notMem_tsupport hq
          simp [angularPhysicalResolventRootCutoffField, hmq])
  simpa only [one_mul] using hcomp
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
