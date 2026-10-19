-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.weightedRealDerivative_integration_by_parts_compact_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/73c92be9-be46-4746-9527-187b0d81a99b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weighted_complex_coordinate_integration_by_parts
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_fderiv_mul_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_mul_weightedRealDerivative_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_of_continuous_compact_cover

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
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedRealDerivative a F v z * G z
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * (fderiv ℝ G z) v
      ∂(coverWeightedMeasure a)) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  have hplain : Integrable
      (fun z : E => (fderiv ℝ F z) v * G z) μ :=
    integrable_fderiv_mul_coverWeightedMeasure
      ha hF hG hGcompact v
  have hpot : Integrable
      (fun z : E =>
        (F z * ((fderiv ℝ a z) v : ℂ)) * G z) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((hF.continuous.mul
        (Complex.continuous_ofReal.comp
          ((ha.continuous_fderiv (by simp)).clm_apply
            continuous_const))).mul hG.continuous)
    exact hGcompact.mul_left
  have hweighted : Integrable
      (fun z : E => F z * weightedRealDerivative a G v z) μ :=
    integrable_mul_weightedRealDerivative_coverWeightedMeasure
      ha hF hG hGcompact v
  have hparts := weighted_complex_coordinate_integration_by_parts
    ha hF hG hGcompact v
  change
    (∫ z : E, weightedRealDerivative a F v z * G z ∂μ) =
      -(∫ z : E, F z * (fderiv ℝ G z) v ∂μ)
  calc
    _ = ∫ z : E,
      ((fderiv ℝ F z) v * G z -
        (F z * ((fderiv ℝ a z) v : ℂ)) * G z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      unfold weightedRealDerivative
      ring
    _ = (∫ z : E, (fderiv ℝ F z) v * G z ∂μ) -
      (∫ z : E, (F z * ((fderiv ℝ a z) v : ℂ)) * G z ∂μ) :=
      MeasureTheory.integral_sub hplain hpot
    _ = -(∫ z : E, F z * weightedRealDerivative a G v z ∂μ) -
      (∫ z : E, (F z * ((fderiv ℝ a z) v : ℂ)) * G z ∂μ) := by
      rw [hparts]
    _ = -((∫ z : E, F z * weightedRealDerivative a G v z ∂μ) +
      (∫ z : E, (F z * ((fderiv ℝ a z) v : ℂ)) * G z ∂μ)) := by
      ring
    _ = -(∫ z : E,
      (F z * weightedRealDerivative a G v z +
        (F z * ((fderiv ℝ a z) v : ℂ)) * G z) ∂μ) :=
      congrArg Neg.neg
        (MeasureTheory.integral_add hweighted hpot).symm
    _ = _ := by
      apply congrArg Neg.neg
      apply integral_congr_ae
      filter_upwards [] with z
      unfold weightedRealDerivative
      ring
end Ehrhart.MatrixTorusBochnerBridge
