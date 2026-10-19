-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeBrascampLieb_of_mem_resolventDefect_closure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/320280a3-593f-4698-97de-9b8decaa2d4d

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_RadialPhysicalResolventDefectReduction_complexHilbert_norm_le_of_mem_closure_inner_bound
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeResolventDefectPairingBound

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusHomogeneousBrascampLieb
open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open EqualitySaturatingKillingPaths ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerIdentity MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBrascampLieb
open MatrixTorusDolbeaultGraph TorusDeckGraphAdjoint TorusFriedrichsCutoff
open RadialPhysicalVelocityCompactGraph RadialPhysicalInverseSquareRootEnergy
open RadialPhysicalResolventRootCutoffPairing RadialPhysicalResolventDefectReduction
open TorusHomogeneousWeakResolventRootCoercivity
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  MatrixOrder InnerProductSpace Topology ContDiff
namespace Ehrhart.TorusHomogeneousBrascampLieb
theorem _root_.solution
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    (hr : MemLp (angularSourceFreeInverseRootGradientField a U)
      2 (angularWeightedTorusMeasure a))
    (hclosure :
      hu.toLp (torusScalarRepresentative U) ∈
        ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
          angularWeakScalarResolventCLM a).range).topologicalClosure) :
    ‖hu.toLp (torusScalarRepresentative U)‖ ≤
      ‖angularSourceFreeInverseRootGradientL2 hr‖ := by
  let f : angularWeightedScalarL2 a :=
    hu.toLp (torusScalarRepresentative U)
  let r : angularWeightedFormL2 a :=
    angularSourceFreeInverseRootGradientL2 hr
  let T : angularWeightedScalarL2 a →L[ℂ]
      angularWeightedScalarL2 a :=
    ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a
  change ‖f‖ ≤ ‖r‖
  have hf : f ∈ closure (T.range : Set (angularWeightedScalarL2 a)) :=
    hclosure
  apply complexHilbert_norm_le_of_mem_closure_inner_bound
    f (T.range : Set (angularWeightedScalarL2 a)) hf (norm_nonneg r)
  intro v hv
  obtain ⟨g, rfl⟩ := hv
  change
    ‖@inner ℂ (angularWeightedScalarL2 a) _ f
      (g - angularWeakScalarResolventCLM a g)‖ ≤
      ‖r‖ * ‖g - angularWeakScalarResolventCLM a g‖
  exact angularSourceFreeResolventDefectPairingBound
    ha ha3 hH hU hperiod hu hr g
end Ehrhart.TorusHomogeneousBrascampLieb
