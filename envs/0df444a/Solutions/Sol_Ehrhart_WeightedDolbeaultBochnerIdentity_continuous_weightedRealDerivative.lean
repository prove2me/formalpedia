-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.continuous_weightedRealDerivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/6449bbd2-a415-4f48-b296-141993f40556

import Mathlib
import Definitions.Def_EhrhartVolumeInequality

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
theorem _root_.solution {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (v : TorusCharacters.LogSpace n) :
    Continuous (weightedRealDerivative a F v) := by
  unfold weightedRealDerivative
  exact ((hF.continuous_fderiv (by simp)).clm_apply
    continuous_const).sub
      (hF.continuous.mul
        (Complex.continuous_ofReal.comp
          ((ha.continuous_fderiv (by simp)).clm_apply
            continuous_const)))
end Ehrhart.WeightedDolbeaultBochnerIdentity
