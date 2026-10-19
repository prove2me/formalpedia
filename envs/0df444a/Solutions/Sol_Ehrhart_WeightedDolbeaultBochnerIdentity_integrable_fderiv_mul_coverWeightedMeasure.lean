-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.integrable_fderiv_mul_coverWeightedMeasure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/f21ac9c6-e293-47f6-83f8-d331f8808cd5

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_coverWeightedMeasure_isLocallyFinite

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
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v * G z)
      (coverWeightedMeasure a) := by
  let : IsLocallyFiniteMeasure (coverWeightedMeasure a) :=
    coverWeightedMeasure_isLocallyFinite ha.continuous
  apply (((hF.continuous_fderiv (by simp)).clm_apply
    continuous_const).mul hG.continuous).integrable_of_hasCompactSupport
  exact hGcompact.mul_left
end Ehrhart.WeightedDolbeaultBochnerIdentity
