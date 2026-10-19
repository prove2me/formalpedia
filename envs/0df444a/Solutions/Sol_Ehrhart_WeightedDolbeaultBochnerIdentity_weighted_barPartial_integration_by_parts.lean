-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_barPartial_integration_by_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/efc0940b-7e0b-403e-9af5-c1a52b3dd108

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weighted_complex_coordinate_integration_by_parts
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weightedAntiholomorphicDerivative_eq_real
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_fderiv_mul_coverWeightedMeasure
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_mul_weightedRealDerivative_coverWeightedMeasure

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
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate F z j * G z
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * weightedAntiholomorphicDerivative a G j z
      ∂(coverWeightedMeasure a)) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hi₀ : Integrable (fun z : E =>
      (fderiv ℝ F z) v₀ * G z) μ :=
    integrable_fderiv_mul_coverWeightedMeasure
      ha hF hG hGcompact v₀
  have hi₁ : Integrable (fun z : E =>
      (fderiv ℝ F z) v₁ * G z) μ :=
    integrable_fderiv_mul_coverWeightedMeasure
      ha hF hG hGcompact v₁
  have hj₀ : Integrable (fun z : E =>
      F z * weightedRealDerivative a G v₀ z) μ :=
    integrable_mul_weightedRealDerivative_coverWeightedMeasure
      ha hF hG hGcompact v₀
  have hj₁ : Integrable (fun z : E =>
      F z * weightedRealDerivative a G v₁ z) μ :=
    integrable_mul_weightedRealDerivative_coverWeightedMeasure
      ha hF hG hGcompact v₁
  have hb₀ := weighted_complex_coordinate_integration_by_parts
    ha hF hG hGcompact v₀
  have hb₁ := weighted_complex_coordinate_integration_by_parts
    ha hF hG hGcompact v₁
  have hleft :
      (∫ z : E, barPartialCoordinate F z j * G z ∂μ) =
        ((∫ z : E, (fderiv ℝ F z) v₀ * G z ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * G z ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        ((fderiv ℝ F z) v₀ * G z +
          Complex.I * ((fderiv ℝ F z) v₁ * G z)) / 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        unfold barPartialCoordinate
        change
          (((fderiv ℝ F z) v₀ +
            Complex.I * (fderiv ℝ F z) v₁) / 2) * G z = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add hi₀
            (hi₁.const_mul Complex.I),
          MeasureTheory.integral_const_mul]
  have hright :
      (∫ z : E, F z *
          weightedAntiholomorphicDerivative a G j z ∂μ) =
        ((∫ z : E,
            F z * weightedRealDerivative a G v₀ z ∂μ) +
          Complex.I *
            (∫ z : E,
              F z * weightedRealDerivative a G v₁ z ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        (F z * weightedRealDerivative a G v₀ z +
          Complex.I *
            (F z * weightedRealDerivative a G v₁ z)) / 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        rw [weightedAntiholomorphicDerivative_eq_real ha z j]
        change
          F z * ((weightedRealDerivative a G v₀ z +
            Complex.I * weightedRealDerivative a G v₁ z) / 2) = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add hj₀
            (hj₁.const_mul Complex.I),
          MeasureTheory.integral_const_mul]
  change
    (∫ z : E, barPartialCoordinate F z j * G z ∂μ) =
      -(∫ z : E,
        F z * weightedAntiholomorphicDerivative a G j z ∂μ)
  calc
    _ = ((∫ z : E, (fderiv ℝ F z) v₀ * G z ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * G z ∂μ)) / 2 := hleft
    _ = -(((∫ z : E,
          F z * weightedRealDerivative a G v₀ z ∂μ) +
          Complex.I *
            (∫ z : E,
              F z * weightedRealDerivative a G v₁ z ∂μ)) / 2) := by
      rw [hb₀, hb₁]
      ring
    _ = _ := congrArg Neg.neg hright.symm
end Ehrhart.WeightedDolbeaultBochnerIdentity
