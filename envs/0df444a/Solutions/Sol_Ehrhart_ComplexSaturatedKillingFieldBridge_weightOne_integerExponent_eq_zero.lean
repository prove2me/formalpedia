-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.weightOne_integerExponent_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/d0a9b1ca-5c0f-4404-b62c-f7a3bcb46d3b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_JointHolomorphicLaurentFourierCompatibility_integerExponent_eq_of_integerPoint

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.ComplexSaturatedKillingFieldBridge
open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology
open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility
namespace Ehrhart.ComplexSaturatedKillingFieldBridge
theorem _root_.solution {n : ℕ}
    (K : CenteredBody n)
    (u : LatticeAsymptotics.monomialIndex K 1) :
    integerExponent K (by decide) u = (0 : Fin n → ℤ) := by
  apply integerExponent_eq_of_integerPoint
    K (by decide) u (0 : Fin n → ℤ)
  have hu := (LatticeAsymptotics.mem_monomialIndex_one_iff
    K (u : Space n)).mp u.property
  rw [hu]
  funext i
  simp [integerPoint]
end Ehrhart.ComplexSaturatedKillingFieldBridge
