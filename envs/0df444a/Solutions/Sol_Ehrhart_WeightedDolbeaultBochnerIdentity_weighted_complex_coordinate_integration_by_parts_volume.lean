-- Prove2me | solution 1 for Ehrhart.WeightedDolbeaultBochnerIdentity.weighted_complex_coordinate_integration_by_parts_volume
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/b4d55b48-f3f5-407c-b589-171e184e688b

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_contDiff_complexCoverWeight
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_fderiv_complexCoverWeight

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
      complexCoverWeight a z * ((fderiv ℝ F z) v * G z)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
    -(∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z *
        (F z * weightedRealDerivative a G v z)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := volume
  let W : E → ℂ := fun z => G z * complexCoverWeight a z
  have hweight : ContDiff ℝ 1 (complexCoverWeight a) :=
    contDiff_complexCoverWeight ha
  have hW : ContDiff ℝ 1 W := hG.mul hweight
  have hWcompact : HasCompactSupport W := by
    change HasCompactSupport (G * complexCoverWeight a)
    exact hGcompact.mul_right
  have hFd : Continuous (fun z : E => (fderiv ℝ F z) v) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hWd : Continuous (fun z : E => (fderiv ℝ W z) v) :=
    (hW.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdfW : Integrable
      (fun z : E => (fderiv ℝ F z) v * W z) μ :=
    (hFd.mul hW.continuous).integrable_of_hasCompactSupport
      hWcompact.mul_left
  have hfDW : Integrable
      (fun z : E => F z * (fderiv ℝ W z) v) μ :=
    (hF.continuous.mul hWd).integrable_of_hasCompactSupport
      (hWcompact.fderiv_apply ℝ v).mul_left
  have hfW : Integrable (fun z : E => F z * W z) μ :=
    (hF.continuous.mul hW.continuous).integrable_of_hasCompactSupport
      hWcompact.mul_left
  have hderiv (z : E) :
      (fderiv ℝ W z) v =
        weightedRealDerivative a G v z * complexCoverWeight a z := by
    have hg := (hG.differentiable (by simp) z).hasFDerivAt
    have hw := (hweight.differentiable (by simp) z).hasFDerivAt
    have hp := congrArg (fun D : E →L[ℝ] ℂ => D v)
      (hg.mul hw).fderiv
    have hp' :
        (fderiv ℝ (G * complexCoverWeight a) z) v =
          G z * (fderiv ℝ (complexCoverWeight a) z) v +
            complexCoverWeight a z * (fderiv ℝ G z) v := by
      simpa only [_root_.add_apply,
        _root_.smul_apply, smul_eq_mul] using hp
    change (fderiv ℝ
      (fun y => G y * complexCoverWeight a y) z) v = _
    change
      (fderiv ℝ (G * complexCoverWeight a) z) v = _
    rw [hp', fderiv_complexCoverWeight ha z v]
    unfold weightedRealDerivative
    ring
  have hip := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (v := v) hdfW hfDW hfW
    (fun z _ => hF.differentiable (by simp) z)
    (fun z _ => hW.differentiable (by simp) z)
  have hleft :
      (∫ z : E, F z * (fderiv ℝ W z) v ∂μ) =
        ∫ z : E, complexCoverWeight a z *
          (F z * weightedRealDerivative a G v z) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    rw [hderiv z]
    ring
  have hright :
      (∫ z : E, (fderiv ℝ F z) v * W z ∂μ) =
        ∫ z : E, complexCoverWeight a z *
          ((fderiv ℝ F z) v * G z) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    change (fderiv ℝ F z) v *
      (G z * complexCoverWeight a z) = _
    ring
  change
    (∫ z : E, complexCoverWeight a z *
      ((fderiv ℝ F z) v * G z) ∂μ) =
    -(∫ z : E, complexCoverWeight a z *
      (F z * weightedRealDerivative a G v z) ∂μ)
  calc
    _ = ∫ z : E, (fderiv ℝ F z) v * W z ∂μ := hright.symm
    _ = -(∫ z : E, F z * (fderiv ℝ W z) v ∂μ) := by
      linear_combination hip
    _ = _ := congrArg Neg.neg hleft
end Ehrhart.WeightedDolbeaultBochnerIdentity
