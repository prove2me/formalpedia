-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeResolventDefectPairingBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/393eab78-8045-4414-a233-45686aeeef36

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousWeakResolventRootCoercivity_angularPhysicalWeakResolventRootCutoffCoercivity
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_tendsto_angularSourceFreeResolventRootCutoff_pairing

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
    (g : angularWeightedScalarL2 a) :
    ‖@inner ℂ (angularWeightedScalarL2 a) _
      (hu.toLp (torusScalarRepresentative U))
      (g - angularWeakScalarResolventCLM a g)‖ ≤
    ‖angularSourceFreeInverseRootGradientL2 hr‖ *
      ‖g - angularWeakScalarResolventCLM a g‖ := by
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  let r : angularWeightedFormL2 a :=
    angularSourceFreeInverseRootGradientL2 hr
  let f : angularWeightedScalarL2 a :=
    hu.toLp (torusScalarRepresentative U)
  change ‖@inner ℂ (angularWeightedScalarL2 a) _ f d‖ ≤
    ‖r‖ * ‖d‖
  rw [norm_inner_symm]
  have hlim :
      Tendsto
        (fun m : ℕ =>
          @inner ℂ (angularWeightedFormL2 a) _ r
            (angularPhysicalResolventRootCutoffL2 ha2 hH W m))
        atTop
        (nhds (@inner ℂ (angularWeightedScalarL2 a) _ d f)) :=
    tendsto_angularSourceFreeResolventRootCutoff_pairing
      ha ha2 hH hU hperiod hu hr g
  have hnorm :
      Tendsto
        (fun m : ℕ =>
          ‖@inner ℂ (angularWeightedFormL2 a) _ r
            (angularPhysicalResolventRootCutoffL2 ha2 hH W m)‖)
        atTop
        (nhds ‖@inner ℂ (angularWeightedScalarL2 a) _ d f‖) :=
    (continuous_norm.tendsto _).comp hlim
  apply le_of_tendsto' hnorm
  intro m
  exact (norm_inner_le_norm r
    (angularPhysicalResolventRootCutoffL2 ha2 hH W m)).trans
      (mul_le_mul_of_nonneg_left
        (angularPhysicalWeakResolventRootCutoffCoercivity
          ha ha3 hH g m)
        (norm_nonneg r))
end Ehrhart.TorusHomogeneousBrascampLieb
