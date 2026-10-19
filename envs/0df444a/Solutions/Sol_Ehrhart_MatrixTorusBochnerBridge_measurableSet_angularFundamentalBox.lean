-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.measurableSet_angularFundamentalBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/8292d985-650e-4683-9535-d09584f95683

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.MatrixTorusBochnerBridge
open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff
namespace Ehrhart.MatrixTorusBochnerBridge
theorem _root_.solution
    {n : ℕ} (b : Space n) :
    MeasurableSet (angularFundamentalBox b) := by
  unfold angularFundamentalBox
  exact MeasurableSet.univ_pi'
    (fun i : Fin n => measurableSet_Ioc)
end Ehrhart.MatrixTorusBochnerBridge
