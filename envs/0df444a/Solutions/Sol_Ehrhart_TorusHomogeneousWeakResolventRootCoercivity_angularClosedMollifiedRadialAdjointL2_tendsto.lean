-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularClosedMollifiedRadialAdjointL2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/09da50a0-917a-4ab4-84a3-b4d411da0d1a

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularClosedMollifiedDrift_fixedRadialCutoff_L2_tendsto_zero
import Theorems.Thm_Ehrhart_TorusHomogeneousCutoffAdjoint_angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousRadialAdjoint_angularClosedMollifiedRadialAdjointCommutatorL2_tendsto
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularClosedMollifiedRadialAdjointL2_eq_defect_drift_commutator

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
    (g : angularWeightedScalarL2 a)
    {B : ℝ}
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
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRadialAdjointL2
          ha ha2 W ℓ m)
      atTop
      (nhds
        (angularWeakSourceCutoffAdjointDefectL2
          d W hB m)) := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  change Tendsto
    (fun ℓ : ℕ =>
      angularClosedMollifiedRadialAdjointL2
        ha ha2 W ℓ m)
    atTop
    (nhds
      (angularWeakSourceCutoffAdjointDefectL2 d W hB m))
  have hscalar :=
    TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
      ha d m
  have hdrift :=
    TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_L2_tendsto_zero
      ha ha2 W m
  have hcomm :=
    TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2_tendsto
      ha W hB m
  have hcombined := (hscalar.neg.add hdrift).add hcomm
  have hlimit :
      Tendsto
        (fun ℓ : ℕ =>
          -(TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_memLp
              ha d m ℓ).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) •
                  torusScalarRepresentative
                    (normalizedCoverMollification
                      (complexTorusCoverLift
                        (fun r : LogTorus n => d r)) ℓ) q) +
            (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
              ha ha2 W ℓ m).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) •
                  torusScalarRepresentative
                    (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) +
            TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2
              ha W ℓ m)
        atTop
        (nhds
          (angularWeakSourceCutoffAdjointDefectL2 d W hB m)) := by
    simpa [angularWeakSourceCutoffAdjointDefectL2] using hcombined
  apply Filter.Tendsto.congr' _ hlimit
  filter_upwards [] with ℓ
  exact (angularClosedMollifiedRadialAdjointL2_eq_defect_drift_commutator
    ha ha3 g ℓ m).symm
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
