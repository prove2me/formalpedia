-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeScalarCutoffGradient_L2_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/c565be72-dbfa-4649-b09b-ff4a405b4cb4

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreConvergence_complexLp_norm_le_of_ae_norm_le

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
    {n : ℕ} {a : LogTorus n → ℝ}
    {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (hperiod : ∀ d : Fin n → ℤ, Function.Periodic U (imaginaryShift d))
    (hu : MemLp (torusScalarRepresentative U) 2
      (angularWeightedTorusMeasure a))
    {C : ℝ} (hCnonneg : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    ‖(angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m).toLp
      (angularSourceFreeScalarCutoffGradient U m)‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) *
        ‖hu.toLp (torusScalarRepresentative U)‖ := by
  apply complexLp_norm_le_of_ae_norm_le
    (angularSourceFreeScalarCutoffGradient_memLp hU hperiod hu m) hu
    (mul_nonneg (by positivity) hCnonneg)
  filter_upwards [] with q
  exact angularSourceFreeScalarCutoffGradient_norm_le U hC m q
end Ehrhart.TorusHomogeneousBrascampLieb
