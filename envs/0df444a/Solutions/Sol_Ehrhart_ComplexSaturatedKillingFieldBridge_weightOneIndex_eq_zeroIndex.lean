-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.weightOneIndex_eq_zeroIndex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/b675033c-f502-4249-9cd7-16657c2f664e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
    u = weightOneZeroIndex K := by
  apply Subtype.ext
  exact (LatticeAsymptotics.mem_monomialIndex_one_iff
    K (u : Space n)).mp u.property
end Ehrhart.ComplexSaturatedKillingFieldBridge
