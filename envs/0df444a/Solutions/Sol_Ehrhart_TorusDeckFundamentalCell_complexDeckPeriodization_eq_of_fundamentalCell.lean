-- Prove2me | solution 1 for Ehrhart.TorusDeckFundamentalCell.complexDeckPeriodization_eq_of_fundamentalCell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:20.297986+00:00
-- url     : https://prove2.me/submissions/c244130f-bf48-4ea0-a0c1-31302df7a8c1

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_TorusDeckFundamentalCell_angularFundamentalBox_integer_shift_eq_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusDeckFundamentalCell
open Set Function Filter MeasureTheory Matrix
open WeightedTorusDistributionBridge TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusDeckFundamentalCell
theorem _root_.solution
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hcell : tsupport ψ ⊆
      {z : TorusCharacters.LogSpace n |
        ((logarithmicCoordinatesEquiv n).symm z).2 ∈
          angularFundamentalBox b})
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b) :
    complexDeckPeriodization ψ
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      ψ (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) := by
  classical
  unfold complexDeckPeriodization
  refine (tsum_eq_single (0 : Fin n → ℤ) ?_).trans ?_
  · intro q hq
    by_contra hnonzero
    have hs := hcell
      (subset_closure ((mem_support).mpr hnonzero))
    rw [← logarithmicPoint_integer_add] at hs
    have hshift :
        (fun i : Fin n => t i + (q i : ℝ)) ∈
          angularFundamentalBox b := by
      change
        ((logarithmicCoordinatesEquiv n).symm
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            x (fun i : Fin n => t i + (q i : ℝ)))).2 ∈
            angularFundamentalBox b at hs
      simpa only [← logarithmicCoordinatesEquiv_apply,
        ContinuousLinearEquiv.symm_apply_apply] using hs
    exact hq (angularFundamentalBox_integer_shift_eq_zero ht hshift)
  · have hzero :
        TorusCharacters.imaginaryShift
          (0 : Fin n → ℤ) = 0 := by
      ext i
      simp [TorusCharacters.imaginaryShift]
    rw [hzero, add_zero]
end Ehrhart.TorusDeckFundamentalCell
