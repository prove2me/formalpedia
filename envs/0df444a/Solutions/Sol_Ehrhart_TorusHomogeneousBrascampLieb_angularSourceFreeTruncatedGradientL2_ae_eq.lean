-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeTruncatedGradientL2_ae_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/5755b086-5af9-47ed-8be9-1e540b2a48bb

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_torusFunctionBarPartialRepresentative_angularSourceFreeScalarRadialGraphTest

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
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a)) (m : ℕ) :
    (fun q : LogTorus n =>
      angularSourceFreeTruncatedGradientL2 ha hU hperiod hu m q) =ᵐ[
        angularWeightedTorusMeasure a]
    (fun q : LogTorus n =>
      (sourceRadialCutoff m q : ℂ) •
        torusFunctionBarPartialRepresentative U q) := by
  let V : LogSpace n → ℂ := angularSourceFreeScalarRadialGraphTest U m
  let hD := angularSourceFreeScalarRadialGraphTest_barPartial_memLp
    ha hU hperiod m
  let hC := angularSourceFreeScalarCutoffGradient_memLp
    hU hperiod hu m
  let A : angularWeightedFormL2 a :=
    angularBarPartialL2OfRepresentative a V hD
  let B : angularWeightedFormL2 a :=
    hC.toLp (angularSourceFreeScalarCutoffGradient U m)
  change (fun q : LogTorus n => (A - B) q) =ᵐ[
    angularWeightedTorusMeasure a] _
  filter_upwards [MeasureTheory.Lp.coeFn_sub A B,
    hD.coeFn_toLp, hC.coeFn_toLp] with q hsub hder hcomm
  rw [hsub]
  change
    (hD.toLp (torusFunctionBarPartialRepresentative V)) q -
      (hC.toLp (angularSourceFreeScalarCutoffGradient U m)) q = _
  rw [hder, hcomm,
    torusFunctionBarPartialRepresentative_angularSourceFreeScalarRadialGraphTest
      hU m q]
  simp
end Ehrhart.TorusHomogeneousBrascampLieb
