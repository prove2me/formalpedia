-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularWeakResolventClosedMollifiedRootBochner_le_adjoint_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/2a5baf7c-ab55-43da-a400-ec57f2e3b01a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusNoncompactBochner_complexScalar_integral_mul_conj_re_eq_L2_norm_sq
import Theorems.Thm_Ehrhart_TorusWeakRadialExteriorMollification_integral_complexEuclideanAntisymmetricEnergy_le_of_memLp
import Theorems.Thm_Ehrhart_TorusHomogeneousSmoothRootBochner_angularWeakResolventClosedMollifiedRootBochner

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
    (g : angularWeightedScalarL2 a)
    (ℓ m : ℕ) :
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    ‖angularClosedMollifiedRootVectorL2
        ha ha2 hH W ℓ m‖ ^ 2 ≤
      ‖angularClosedMollifiedRadialAdjointL2
          ha ha2 W ℓ m‖ ^ 2 +
        2 * ‖TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2
          ha W ℓ m‖ ^ 2 := by
  dsimp only
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  have hadj := angularClosedMollifiedRadialAdjoint_memLp
    ha ha2 W ℓ m
  have hmatrix :=
    TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutator_memLp
      ha W ℓ m
  have hboch :=
    TorusHomogeneousSmoothRootBochner.angularWeakResolventClosedMollifiedRootBochner
      ha ha2 hH g ℓ m
  change
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤ _ at hboch ⊢
  calc
    _ ≤
        (∫ q : LogTorus n,
          angularTorusFormAdjoint a
            (cutoffPhysicalField m
              (angularGraphMollifiedPhysicalField W ℓ)) q *
            conj (angularTorusFormAdjoint a
              (cutoffPhysicalField m
                (angularGraphMollifiedPhysicalField W ℓ)) q)
          ∂(angularWeightedTorusMeasure a)).re +
        (∫ q : LogTorus n,
          complexEuclideanAntisymmetricEnergy
            (sourceCutoffDerivativeCommutator m
              (angularGraphMollifiedPhysicalField W ℓ) q)
          ∂(angularWeightedTorusMeasure a)).re := hboch
    _ ≤
        (∫ q : LogTorus n,
          angularTorusFormAdjoint a
            (cutoffPhysicalField m
              (angularGraphMollifiedPhysicalField W ℓ)) q *
            conj (angularTorusFormAdjoint a
              (cutoffPhysicalField m
                (angularGraphMollifiedPhysicalField W ℓ)) q)
          ∂(angularWeightedTorusMeasure a)).re +
        2 * ‖hmatrix.toLp
          (sourceCutoffDerivativeCommutator m
            (angularGraphMollifiedPhysicalField W ℓ))‖ ^ 2 :=
      add_le_add le_rfl
        (integral_complexEuclideanAntisymmetricEnergy_le_of_memLp
          hmatrix)
    _ = _ := by
      rw [complexScalar_integral_mul_conj_re_eq_L2_norm_sq hadj]
      rfl
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
