-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularClosedMollifiedRootVector_sub_pointwise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.345565+00:00
-- url     : https://prove2.me/submissions/cb25f628-6b58-4412-8600-3948ec635148

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeakResolventRootBochner_angularEuclideanConjugation_sub
import Theorems.Thm_Ehrhart_TorusWeakResolventRootBochner_angularEuclideanConjugation_real_smul

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
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    angularSmoothCompactHessianRootVector a
        (angularGraphMollifiedPhysicalField W ℓ) m q -
      angularPhysicalResolventRootCutoffField a W m q =
      (sourceRadialCutoff m q : ℂ) •
        Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation
            (torusFormRepresentative
                (angularGraphMollifiedPhysicalField W ℓ) q - W q)) := by
  rw [angularSmoothCompactHessianRootVector,
    angularPhysicalResolventRootCutoffField]
  change
    Matrix.toEuclideanLin
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q)
        (angularEuclideanConjugation
          (torusFormRepresentative
            (cutoffPhysicalField m
              (angularGraphMollifiedPhysicalField W ℓ)) q)) -
      (sourceRadialCutoff m q : ℂ) •
        Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q)) = _
  rw [torusFormRepresentative_cutoffPhysicalField,
    angularEuclideanConjugation_real_smul,
    map_smul, ← smul_sub, ← map_sub,
    ← angularEuclideanConjugation_sub]
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
