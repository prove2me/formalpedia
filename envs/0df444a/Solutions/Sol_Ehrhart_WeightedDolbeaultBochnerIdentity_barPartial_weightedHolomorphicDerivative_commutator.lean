-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.barPartial_weightedHolomorphicDerivative_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:14.10863+00:00
-- url     : https://prove2.me/submissions/db48f920-c7f5-412e-bfea-5bc12aceb563

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_holomorphic_commute
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_barPartial_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.WeightedDolbeaultBochnerIdentity
open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate
namespace Ehrhart.WeightedDolbeaultBochnerIdentity
theorem _root_.solution
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 2 a)
    (hF : ContDiff ℝ 2 F)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    barPartialCoordinate
      (fun w => weightedHolomorphicDerivative a F i w) z j =
      weightedHolomorphicDerivative a
        (fun w => barPartialCoordinate F w j) i z -
          F z * complexHessian a z i j := by
  have haone : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hfone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hac : ContDiff ℝ 2 (fun w => (a w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  have hholF := contDiff_holomorphicCoordinate hF i
  have hholA := contDiff_holomorphicCoordinate hac i
  change
    barPartialCoordinate
      (fun w => holomorphicCoordinate F w i -
        F w * holomorphicCoordinate (fun ξ => (a ξ : ℂ)) w i)
      z j = _
  rw [barPartial_sub hholF (hfone.mul hholA) z j,
    barPartial_mul hfone hholA z j,
    barPartial_holomorphic_commute hF z i j]
  unfold weightedHolomorphicDerivative complexHessian
  ring
end Ehrhart.WeightedDolbeaultBochnerIdentity
