-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeScalarRadialGraphTest_scalar_L2_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/9cb07563-d0b3-4e2a-b4fb-627d107df33e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularSourceRadialCutoff_smul_L2_tendsto

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
      (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        angularScalarL2OfRepresentative a
          (angularSourceFreeScalarRadialGraphTest U m)
          (angularSourceFreeScalarRadialGraphTest_scalar_memLp
            ha hU hperiod m))
      atTop (nhds (hu.toLp (torusScalarRepresentative U))) := by
  have hcut := angularSourceRadialCutoff_smul_L2_tendsto hu
  apply Filter.Tendsto.congr' _ hcut
  filter_upwards [] with m
  unfold angularScalarL2OfRepresentative
  apply MemLp.toLp_congr
  filter_upwards [] with q
  rw [torusScalarRepresentative_angularSourceFreeScalarRadialGraphTest]
  simp [smul_eq_mul]
end Ehrhart.TorusHomogeneousBrascampLieb
