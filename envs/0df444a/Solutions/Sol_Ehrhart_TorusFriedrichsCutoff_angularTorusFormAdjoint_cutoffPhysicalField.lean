-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsCutoff.angularTorusFormAdjoint_cutoffPhysicalField
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/69030681-a022-417c-8f58-06cae24d5cb1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularTorusWeightedHolomorphicDerivative_cutoffPhysicalField
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_angularSourceCutoffAdjointCommutator_eq_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusFriedrichsCutoff
open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters JetEnvelopeRightDerivative EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
namespace Ehrhart.TorusFriedrichsCutoff
theorem _root_.solution
    {n : ℕ} (a : LogTorus n → ℝ) (m : ℕ)
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W) (q : LogTorus n) :
    angularTorusFormAdjoint a (cutoffPhysicalField m W) q =
      (sourceRadialCutoff m q : ℂ) *
        angularTorusFormAdjoint a W q +
      angularSourceCutoffAdjointCommutator m W q := by
  unfold angularTorusFormAdjoint
  simp_rw [angularTorusWeightedHolomorphicDerivative_cutoffPhysicalField
    a m hW]
  rw [angularSourceCutoffAdjointCommutator_eq_sum]
  simp [Finset.sum_add_distrib, ← Finset.mul_sum]
end Ehrhart.TorusFriedrichsCutoff
