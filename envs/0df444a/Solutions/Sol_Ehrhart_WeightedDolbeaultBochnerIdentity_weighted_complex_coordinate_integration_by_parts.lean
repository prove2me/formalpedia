-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_complex_coordinate_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/3f830b6b-889d-48d7-bb83-177d83af3c2e

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integral_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weighted_complex_coordinate_integration_by_parts_volume

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
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      (fderiv ℝ F z) v * G z ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * weightedRealDerivative a G v z
      ∂(coverWeightedMeasure a)) := by
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z * ((fderiv ℝ F z) v * G z)
      ∂(volume : Measure (TorusCharacters.LogSpace n)) :=
        integral_coverWeightedMeasure ha.continuous _
    _ = -(∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z *
        (F z * weightedRealDerivative a G v z)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) :=
        weighted_complex_coordinate_integration_by_parts_volume
          ha hF hG hGcompact v
    _ = _ := congrArg Neg.neg
      (integral_coverWeightedMeasure ha.continuous _).symm
end Ehrhart.WeightedDolbeaultBochnerIdentity
