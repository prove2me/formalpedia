-- Prove2me | solution 1 for Ehrhart.DolbeaultGraphDistributionBridge.complex_compact_barPartial_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/feaa07a9-6885-4173-bed2-33cde0168e36

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultGraphDistributionBridge_complex_compact_integration_by_parts

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.DolbeaultGraphDistributionBridge
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths DolbeaultRegularity
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultGraphDistributionBridge
theorem _root_.solution {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      F z * coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : TorusCharacters.LogSpace n,
          barPartialCoordinate F z j * (ψ z : ℂ)
          ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := volume
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hψd₀ : Continuous
      (fun z : E => ((fderiv ℝ ψ z) v₀ : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hψd₁ : Continuous
      (fun z : E => ((fderiv ℝ ψ z) v₁ : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hc₀ : HasCompactSupport
      (fun z : E => ((fderiv ℝ ψ z) v₀ : ℂ)) :=
    compactSupport_complexOfReal (hψcompact.fderiv_apply ℝ v₀)
  have hc₁ : HasCompactSupport
      (fun z : E => ((fderiv ℝ ψ z) v₁ : ℂ)) :=
    compactSupport_complexOfReal (hψcompact.fderiv_apply ℝ v₁)
  have hi₀ : Integrable
      (fun z : E => F z * ((fderiv ℝ ψ z) v₀ : ℂ)) μ :=
    (hF.continuous.mul hψd₀).integrable_of_hasCompactSupport
      hc₀.mul_left
  have hi₁ : Integrable
      (fun z : E => F z * ((fderiv ℝ ψ z) v₁ : ℂ)) μ :=
    (hF.continuous.mul hψd₁).integrable_of_hasCompactSupport
      hc₁.mul_left
  have hF₀ : Continuous
      (fun z : E => (fderiv ℝ F z) v₀) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hF₁ : Continuous
      (fun z : E => (fderiv ℝ F z) v₁) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψC : Continuous (fun z : E => (ψ z : ℂ)) :=
    Complex.continuous_ofReal.comp hψ.continuous
  have hψCc : HasCompactSupport (fun z : E => (ψ z : ℂ)) :=
    compactSupport_complexOfReal hψcompact
  have hd₀ : Integrable
      (fun z : E => (fderiv ℝ F z) v₀ * (ψ z : ℂ)) μ :=
    (hF₀.mul hψC).integrable_of_hasCompactSupport hψCc.mul_left
  have hd₁ : Integrable
      (fun z : E => (fderiv ℝ F z) v₁ * (ψ z : ℂ)) μ :=
    (hF₁.mul hψC).integrable_of_hasCompactSupport hψCc.mul_left
  have hip₀ := complex_compact_integration_by_parts
    hF hψ hψcompact v₀
  have hip₁ := complex_compact_integration_by_parts
    hF hψ hψcompact v₁
  change
    (∫ z : E,
      F z *
        (((fderiv ℝ ψ z) v₀ : ℂ) +
          Complex.I * ((fderiv ℝ ψ z) v₁ : ℂ)) ∂μ) =
      -(2 : ℂ) *
        (∫ z : E, barPartialCoordinate F z j * (ψ z : ℂ) ∂μ)
  have hleft :
      (∫ z : E,
        F z *
          (((fderiv ℝ ψ z) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ ψ z) v₁ : ℂ)) ∂μ) =
        (∫ z : E, F z * ((fderiv ℝ ψ z) v₀ : ℂ) ∂μ) +
          Complex.I *
            (∫ z : E, F z * ((fderiv ℝ ψ z) v₁ : ℂ) ∂μ) := by
    calc
      _ = ∫ z : E,
        (F z * ((fderiv ℝ ψ z) v₀ : ℂ)) +
          Complex.I * (F z * ((fderiv ℝ ψ z) v₁ : ℂ)) ∂μ := by
            congr 1
            funext z
            ring
      _ = _ := by
        rw [integral_add hi₀ (hi₁.const_mul Complex.I),
          integral_const_mul]
  have hright :
      (∫ z : E, barPartialCoordinate F z j * (ψ z : ℂ) ∂μ) =
        ((∫ z : E, (fderiv ℝ F z) v₀ * (ψ z : ℂ) ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * (ψ z : ℂ) ∂μ)) / 2 := by
    unfold barPartialCoordinate
    calc
      _ = ∫ z : E,
        (((fderiv ℝ F z) v₀ * (ψ z : ℂ)) +
          Complex.I *
            ((fderiv ℝ F z) v₁ * (ψ z : ℂ))) / 2 ∂μ := by
            congr 1
            funext z
            ring
      _ = _ := by
        rw [integral_div,
          integral_add hd₀ (hd₁.const_mul Complex.I),
          integral_const_mul]
  rw [hleft, hright]
  change
    (∫ z : E, F z * ((fderiv ℝ ψ z) v₀ : ℂ) ∂μ) +
        Complex.I *
          (∫ z : E, F z * ((fderiv ℝ ψ z) v₁ : ℂ) ∂μ) =
      -(2 : ℂ) *
        (((∫ z : E, (fderiv ℝ F z) v₀ * (ψ z : ℂ) ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * (ψ z : ℂ) ∂μ)) / 2)
  rw [hip₀, hip₁]
  ring
end Ehrhart.DolbeaultGraphDistributionBridge
