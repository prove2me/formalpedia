-- Prove2me | solution 1 for Ehrhart.TorusDeckFullCellDerivative.barPartial_complexDeckPeriodization_eq_on_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/47e403fd-30f8-46a2-a520-f195b791653f

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckFullCellDerivative_complexDeckPeriodization_eventuallyEq_on_fundamentalCell

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckFullCellDerivative
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge TorusDeckPeriodization TorusDeckFundamentalCell
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff
namespace Ehrhart.TorusDeckFullCellDerivative
theorem _root_.solution
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b)
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b)
    (j : Fin n) :
    barPartialCoordinate (complexDeckPeriodization ψ)
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) j =
      barPartialCoordinate ψ
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t) j := by
  have hd :=
    (complexDeckPeriodization_eventuallyEq_on_fundamentalCell
      hψcompact hcell x t ht).fderiv_eq (𝕜 := ℝ)
  unfold barPartialCoordinate
  rw [hd]
end Ehrhart.TorusDeckFullCellDerivative
