-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/891d2db7-6c14-44f7-a094-bf647640d73d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousRadialMatrix_angularClosedMollifiedRadialMatrixCommutatorL2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularClosedMollifiedRootVectorL2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularClosedMollifiedRadialAdjointL2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularWeakResolventClosedMollifiedRootBochner_le_adjoint_matrix

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
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    let d : angularWeightedScalarL2 a :=
      g - angularWeakScalarResolventCLM a g
    ‖angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤
      ‖angularWeakSourceCutoffAdjointDefectL2 d W hB m‖ ^ 2 +
        2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
          W hB m).toLp
            (angularWeakSourceCutoffDerivativeCommutator W m)‖ ^ 2 := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  let R : angularWeightedFormL2 a :=
    angularPhysicalResolventRootCutoffL2 ha2 hH W m
  let J : angularWeightedScalarL2 a :=
    angularWeakSourceCutoffAdjointDefectL2 d W hB m
  let M : MeasureTheory.Lp
      (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (angularWeightedTorusMeasure a) :=
    (angularWeakSourceCutoffDerivativeCommutator_memLp
      W hB m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)
  have hroot := angularClosedMollifiedRootVectorL2_tendsto
    ha ha2 hH W m
  have hrootnorm :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRootVectorL2
            ha ha2 hH W ℓ m‖ ^ 2)
        atTop (nhds (‖R‖ ^ 2)) := by
    exact ((continuous_norm.tendsto R).comp hroot).pow 2
  have hadj := angularClosedMollifiedRadialAdjointL2_tendsto
    ha ha3 g hB m
  have hadjnorm :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRadialAdjointL2
            ha ha2 W ℓ m‖ ^ 2)
        atTop (nhds (‖J‖ ^ 2)) := by
    exact ((continuous_norm.tendsto J).comp hadj).pow 2
  have hmatrix :=
    TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2_tendsto
      ha W hB₀ hB m
  have hmatrixnorm :
      Tendsto
        (fun ℓ : ℕ =>
          2 * ‖TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2
            ha W ℓ m‖ ^ 2)
        atTop (nhds (2 * ‖M‖ ^ 2)) := by
    exact (((continuous_norm.tendsto M).comp hmatrix).pow 2).const_mul 2
  have hlimit := (hadjnorm.add hmatrixnorm).sub hrootnorm
  have hnonneg : 0 ≤ ‖J‖ ^ 2 + 2 * ‖M‖ ^ 2 - ‖R‖ ^ 2 := by
    apply ge_of_tendsto hlimit
    filter_upwards [] with ℓ
    exact sub_nonneg.mpr
      (angularWeakResolventClosedMollifiedRootBochner_le_adjoint_matrix
        ha ha2 hH g ℓ m)
  exact sub_nonneg.mp hnonneg
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
