-- Prove2me | solution 1 for Ehrhart.ComplexSaturatedKillingFieldBridge.torusMonomial_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:18.423054+00:00
-- url     : https://prove2.me/submissions/390f2cb7-9535-44e6-9e9c-d59bc0b7c08e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusCharacters_torusCharacter_zero

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
    (p : WeightedTorusHilbert.LogTorus n) :
    torusMonomial (0 : Fin n → ℤ) p = 1 := by
  simp [torusMonomial, radialCharacter,
    TorusCharacters.torusCharacter_zero,
    UnitAddTorus.mFourier_zero]
end Ehrhart.ComplexSaturatedKillingFieldBridge
