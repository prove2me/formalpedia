-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerIdentity.angularCoverProjection_binary_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/6cc60828-a37b-4b81-a575-57c12fbb4f51

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerIdentity
open Set Function MeasureTheory Filter Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerIdentity
theorem _root_.solution
    {n : ℕ} (q : Fin n → Bool) (t : Space n) :
    angularCoverProjection n
      (binaryAngularFundamentalBase q + t) =
      angularCoverProjection n t := by
  let u : Fin n → ℤ :=
    fun i => if q i then (-1 : ℤ) else 0
  have heq :
      binaryAngularFundamentalBase q + t =
        fun i : Fin n => t i + (u i : ℝ) := by
    funext i
    simp only [Pi.add_apply, binaryAngularFundamentalBase, u]
    split <;> simp ; ring
  rw [heq, angularCoverProjection_integer_add]
end Ehrhart.MatrixTorusBochnerIdentity
