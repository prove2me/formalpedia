-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularClosedMollifiedRadialAdjointL2_eq_defect_drift_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/6870cca8-51da-4a21-b0d7-d4f755c46627

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusStrongWeightedCutoffAdjoint_torusScalarRepresentative_eq_sourceTorusCoverPoint
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularTorusFormAdjoint_cutoff_closedWeakResolventMollifier

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
    (ℓ m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    let d : angularWeightedScalarL2 a :=
      g - angularWeakScalarResolventCLM a g
    angularClosedMollifiedRadialAdjointL2 ha ha2 W ℓ m =
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
          ha W ℓ m := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  let U : angularWeightedScalarL2 a :=
    angularClosedMollifiedRadialAdjointL2 ha ha2 W ℓ m
  let P : angularWeightedScalarL2 a :=
    (TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_memLp
      ha d m ℓ).toLp
        (fun q : LogTorus n =>
          (sourceRadialCutoff m q : ℂ) •
            torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n => d r)) ℓ) q)
  let T : angularWeightedScalarL2 a :=
    (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
      ha ha2 W ℓ m).toLp
        (fun q : LogTorus n =>
          (sourceRadialCutoff m q : ℂ) •
            torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q)
  let J : angularWeightedScalarL2 a :=
    TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2
      ha W ℓ m
  change U = -P + T + J
  apply MeasureTheory.Lp.ext
  have hU :=
    (angularClosedMollifiedRadialAdjoint_memLp
      ha ha2 W ℓ m).coeFn_toLp
  have hP :=
    (TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_memLp
      ha d m ℓ).coeFn_toLp
  have hT :=
    (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
      ha ha2 W ℓ m).coeFn_toLp
  have hJ :=
    (TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutator_memLp
      ha W ℓ m).coeFn_toLp
  filter_upwards
    [hU, hP, hT, hJ,
     MeasureTheory.Lp.coeFn_neg P,
     MeasureTheory.Lp.coeFn_add (-P) T,
     MeasureTheory.Lp.coeFn_add (-P + T) J]
    with q hu hp ht hj hneg hinner houter
  change U q =
    angularTorusFormAdjoint a
      (cutoffPhysicalField m
        (angularGraphMollifiedPhysicalField W ℓ)) q at hu
  change P q =
    (sourceRadialCutoff m q : ℂ) •
      torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => d r)) ℓ) q at hp
  change T q =
    (sourceRadialCutoff m q : ℂ) •
      torusScalarRepresentative
        (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q at ht
  change J q =
    angularSourceCutoffAdjointCommutator m
      (angularGraphMollifiedPhysicalField W ℓ) q at hj
  rw [hu, houter, Pi.add_apply, hinner, Pi.add_apply,
    hneg, Pi.neg_apply, hp, ht, hj]
  have hpoint :=
    angularTorusFormAdjoint_cutoff_closedWeakResolventMollifier
      ha ha3 g ℓ m q
  change
    angularTorusFormAdjoint a
      (cutoffPhysicalField m
        (angularGraphMollifiedPhysicalField W ℓ)) q =
      (sourceRadialCutoff m q : ℂ) *
        (-normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => d r)) ℓ
            (sourceTorusCoverPoint q) +
          angularMollifiedPhysicalAdjointDriftCommutator
            W ℓ (sourceTorusCoverPoint q)) +
        angularSourceCutoffAdjointCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q
    at hpoint
  rw [hpoint]
  simp only [torusScalarRepresentative_eq_sourceTorusCoverPoint,
    smul_eq_mul]
  ring
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
