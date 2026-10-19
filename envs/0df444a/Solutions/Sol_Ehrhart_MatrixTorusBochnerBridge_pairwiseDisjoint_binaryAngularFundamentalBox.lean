-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.pairwiseDisjoint_binaryAngularFundamentalBox
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/bb3d88e3-00ac-4ebb-b42a-1dc411a5acaa

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
    (n : ℕ) :
    Pairwise
      (Disjoint on
        (fun q : Fin n → Bool =>
          angularFundamentalBox (binaryAngularFundamentalBase q))) := by
  classical
  intro q r hqr
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hqr
  apply Set.disjoint_left.mpr
  intro t hq hr
  have hqi := hq i
  have hri := hr i
  change
    t i ∈ Set.Ioc
      (if q i then (-1 : ℝ) else 0)
      ((if q i then (-1 : ℝ) else 0) + 1) at hqi
  change
    t i ∈ Set.Ioc
      (if r i then (-1 : ℝ) else 0)
      ((if r i then (-1 : ℝ) else 0) + 1) at hri
  cases hqval : q i <;> cases hrval : r i <;>
    simp_all [Set.mem_Ioc] <;> linarith
end Ehrhart.MatrixTorusBochnerBridge
