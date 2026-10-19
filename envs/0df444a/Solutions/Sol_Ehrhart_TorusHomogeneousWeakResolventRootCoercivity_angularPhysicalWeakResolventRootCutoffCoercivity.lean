-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularPhysicalWeakResolventRootCutoffCoercivity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/079dc22e-0539-41b2-83c5-f5def6c6fb13

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusWeakRadialCutoffCommutator_angularWeakSourceCutoffDerivativeCommutator_L2_tendsto_zero
import Theorems.Thm_Ehrhart_TorusWeakRadialBochnerUpperBound_angularWeakSourceCutoffAdjointDefectL2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_eventually_angularPhysicalResolventRootCutoffL2_norm_le

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
    (m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    ‖angularPhysicalResolventRootCutoffL2
      ha2 hH W m‖ ≤
      ‖g - angularWeakScalarResolventCLM a g‖ := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  change ‖angularPhysicalResolventRootCutoffL2 ha2 hH W m‖ ≤ ‖d‖
  obtain ⟨B, hB₀, hB⟩ :=
    unitBump_euclideanGradient_bound (n := n)
  have hadj :=
    angularWeakSourceCutoffAdjointDefectL2_tendsto
      d W hB₀ hB
  have hadjnorm :=
    ((continuous_norm.tendsto
      (-d : angularWeightedScalarL2 a)).comp hadj).pow 2
  have hmatrix :=
    angularWeakSourceCutoffDerivativeCommutator_L2_tendsto_zero
      W hB₀ hB
  have hmatrixnorm :=
    (((continuous_norm.tendsto
      (0 : MeasureTheory.Lp
        (EuclideanSpace ℂ (Fin n × Fin n)) 2
        (angularWeightedTorusMeasure a))).comp hmatrix).pow 2).const_mul
      (2 : ℝ)
  have htail :
      Tendsto
        (fun M : ℕ =>
          ‖angularWeakSourceCutoffAdjointDefectL2
            d W hB M‖ ^ 2 +
          2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
            W hB M).toLp
              (angularWeakSourceCutoffDerivativeCommutator W M)‖ ^ 2)
        atTop (nhds (‖d‖ ^ 2)) := by
    simpa using hadjnorm.add hmatrixnorm
  have hbound :
      ∀ᶠ M : ℕ in atTop,
        ‖angularPhysicalResolventRootCutoffL2
          ha2 hH W m‖ ^ 2 ≤
          ‖angularWeakSourceCutoffAdjointDefectL2
            d W hB M‖ ^ 2 +
          2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
            W hB M).toLp
              (angularWeakSourceCutoffDerivativeCommutator W M)‖ ^ 2 := by
    filter_upwards
      [eventually_angularPhysicalResolventRootCutoffL2_norm_le
        ha2 hH W m]
      with M hmono
    calc
      ‖angularPhysicalResolventRootCutoffL2
          ha2 hH W m‖ ^ 2 ≤
        ‖angularPhysicalResolventRootCutoffL2
          ha2 hH W M‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmono
      _ ≤ _ :=
        angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
          ha ha3 hH g hB₀ hB M
  have hsquare :
      ‖angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    ge_of_tendsto htail hbound
  exact
    (sq_le_sq₀
      (norm_nonneg
        (angularPhysicalResolventRootCutoffL2 ha2 hH W m))
      (norm_nonneg d)).mp hsquare
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
