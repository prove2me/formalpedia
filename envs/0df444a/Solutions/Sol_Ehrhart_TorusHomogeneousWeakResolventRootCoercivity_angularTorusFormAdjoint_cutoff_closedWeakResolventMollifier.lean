-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousWeakResolventRootCoercivity.angularTorusFormAdjoint_cutoff_closedWeakResolventMollifier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:22.994904+00:00
-- url     : https://prove2.me/submissions/f209270f-64fd-4635-a2f4-9dd4df62e691

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularTorusFormAdjoint_cutoffPhysicalField
import Theorems.Thm_Ehrhart_TorusClosedMollifiedRootBochner_angularTorusFormAdjoint_eq_coverFormAdjoint
import Theorems.Thm_Ehrhart_TorusHomogeneousClosedResolventAdjoint_coverFormAdjoint_angularGraphMollifiedPhysicalWeakResolvent_eq

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
    (ℓ m : ℕ) (q : LogTorus n) :
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    angularTorusFormAdjoint a
      (cutoffPhysicalField m
        (angularGraphMollifiedPhysicalField W ℓ)) q =
      (sourceRadialCutoff m q : ℂ) *
        (-normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n =>
              (g - angularWeakScalarResolventCLM a g) r))
          ℓ (sourceTorusCoverPoint q) +
          angularMollifiedPhysicalAdjointDriftCommutator
            W ℓ (sourceTorusCoverPoint q)) +
        angularSourceCutoffAdjointCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q := by
  dsimp only
  rw [angularTorusFormAdjoint_cutoffPhysicalField a m
    (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha
      (WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)) ℓ 2) q,
    angularTorusFormAdjoint_eq_coverFormAdjoint,
    TorusHomogeneousClosedResolventAdjoint.coverFormAdjoint_angularGraphMollifiedPhysicalWeakResolvent_eq
      ha ha3 g ℓ (sourceTorusCoverPoint q)]
end Ehrhart.TorusHomogeneousWeakResolventRootCoercivity
