-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.angularSourceFreeScalarCutoffGradient_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/2c0beac6-a1fd-41db-93f7-cd565a141b78

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedResolventConstantCore_inv_nat_add_one_tendsto_zero
import Theorems.Thm_Ehrhart_TorusHomogeneousBrascampLieb_angularSourceFreeScalarCutoffGradient_L2_norm_le

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
      (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        (angularSourceFreeScalarCutoffGradient_memLp
          hU hperiod hu m).toLp
            (angularSourceFreeScalarCutoffGradient U m))
      atTop (nhds (0 : angularWeightedFormL2 a)) := by
  obtain ⟨C, hCnonneg, hC⟩ :=
    unitBump_euclideanGradient_bound (n := n)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => angularSourceFreeScalarCutoffGradient_L2_norm_le
      hU hperiod hu hCnonneg hC m)
  have hz := inv_nat_add_one_tendsto_zero.mul_const
    (C * ‖hu.toLp (torusScalarRepresentative U)‖)
  simpa [mul_assoc] using hz
end Ehrhart.TorusHomogeneousBrascampLieb
