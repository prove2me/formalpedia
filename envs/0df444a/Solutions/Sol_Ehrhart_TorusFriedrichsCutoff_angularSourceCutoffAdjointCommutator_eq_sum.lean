-- Prove2me | solution 1 for Ehrhart.TorusFriedrichsCutoff.angularSourceCutoffAdjointCommutator_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/fcb718f5-9ae6-43f5-8672-ccd123ae9ab5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusFriedrichsCutoff_torusHolomorphicDerivative_complexSourceCoverRadialCutoff

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
    {n : ℕ} (m : ℕ)
    (W : LogSpace n → LogSpace n)
    (q : LogTorus n) :
    angularSourceCutoffAdjointCommutator m W q =
      ∑ i : Fin n,
        torusScalarRepresentative (fun z => W z i) q *
          torusScalarRepresentative
            (fun z => holomorphicCoordinate
              (complexSourceCoverRadialCutoff m) z i) q := by
  unfold angularSourceCutoffAdjointCommutator
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [torusHolomorphicDerivative_complexSourceCoverRadialCutoff]
  rfl
end Ehrhart.TorusFriedrichsCutoff
