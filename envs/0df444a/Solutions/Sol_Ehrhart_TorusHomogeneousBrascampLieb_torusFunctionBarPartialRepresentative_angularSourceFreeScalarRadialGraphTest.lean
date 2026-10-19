-- Prove2me | solution 1 for Ehrhart.TorusHomogeneousBrascampLieb.torusFunctionBarPartialRepresentative_angularSourceFreeScalarRadialGraphTest
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:23.737149+00:00
-- url     : https://prove2.me/submissions/fd835e50-da74-41a2-b864-a93939564e1e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_mul
import Theorems.Thm_Ehrhart_MatrixTorusBochnerCoreApproximation_torusScalarRepresentative_add

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
    {n : ℕ} {U : LogSpace n → ℂ} (hU : ContDiff ℝ 3 U)
    (m : ℕ) (q : LogTorus n) :
    torusFunctionBarPartialRepresentative
      (angularSourceFreeScalarRadialGraphTest U m) q =
      (sourceRadialCutoff m q : ℂ) •
        torusFunctionBarPartialRepresentative U q +
      angularSourceFreeScalarCutoffGradient U m q := by
  ext j
  change
    sourceTorusBarPartial
      (angularSourceFreeScalarRadialGraphTest U m) j q =
      (sourceRadialCutoff m q : ℂ) *
        sourceTorusBarPartial U j q +
      torusScalarRepresentative U q *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) j q
  have hprod :
      (fun z : LogSpace n =>
        barPartialCoordinate
          (angularSourceFreeScalarRadialGraphTest U m) z j) =
      fun z : LogSpace n =>
        complexSourceCoverRadialCutoff m z *
            barPartialCoordinate U z j +
          U z *
            barPartialCoordinate
              (complexSourceCoverRadialCutoff m) z j := by
    funext z
    unfold angularSourceFreeScalarRadialGraphTest
    rw [barPartial_mul
      (contDiff_complexSourceCoverRadialCutoff_all m 1)
      (hU.of_le (by norm_num)) z j]
    ring
  unfold sourceTorusBarPartial
  change torusScalarRepresentative
    (fun z : LogSpace n =>
      barPartialCoordinate
        (angularSourceFreeScalarRadialGraphTest U m) z j) q = _
  rw [hprod, torusScalarRepresentative_add,
    torusScalarRepresentative_mul, torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]
end Ehrhart.TorusHomogeneousBrascampLieb
