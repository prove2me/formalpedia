-- Prove2me | solution 1 for Ehrhart.TorusWeakDolbeaultMollification.barPartial_complexReal_convolution_eq_of_compact_green
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:19.434976+00:00
-- url     : https://prove2.me/submissions/b822891e-af4d-4767-aa73-ac8ec34f2139

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexRealMultiplication_apply
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_contDiff
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_hasCompactSupport
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_fderiv

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeakDolbeaultMollification
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths DolbeaultRegularity DolbeaultGraphDistributionBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusWeakDolbeaultMollification
theorem _root_.solution
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {G : Fin n → TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : ∀ (ψ : TorusCharacters.LogSpace n → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ j : Fin n,
        (∫ t : TorusCharacters.LogSpace n,
          g t * coverBarPartialTest ψ j t
          ∂(volume : Measure (TorusCharacters.LogSpace n))) =
        -(2 : ℂ) *
          (∫ t : TorusCharacters.LogSpace n,
            G j t * (ψ t : ℂ)
            ∂(volume : Measure (TorusCharacters.LogSpace n))))
    (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      x j =
    (G j ⋆[complexRealMultiplication,
      (volume : Measure (TorusCharacters.LogSpace n))] κ) x := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := volume
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := complexRealMultiplication
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have htest := hweak
    (fun t : E => κ (x - t))
    (translatedRealKernel_contDiff hκ x)
    (translatedRealKernel_hasCompactSupport hκcompact x) j
  have hnegative :
      (∫ t : E,
        -(g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ)))
          ∂μ) =
      -(2 : ℂ) *
        (∫ t : E, G j t * (κ (x - t) : ℂ) ∂μ) := by
    simpa only [E, μ, v₀, v₁, coverBarPartialTest,
      translatedRealKernel_fderiv hκ x,
      Complex.ofReal_neg, mul_neg, ← neg_add] using htest
  have hpositive :
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ))
          ∂μ) =
      (2 : ℂ) *
        (∫ t : E, G j t * (κ (x - t) : ℂ) ∂μ) := by
    rw [integral_neg] at hnegative
    linear_combination -hnegative
  have hderiv := hκcompact.hasFDerivAt_convolution_right
    L hg hκ x
  have hint : Integrable
      (fun t : E =>
        (L.precompR E) (g t) (fderiv ℝ κ (x - t))) μ :=
    (hκcompact.fderiv ℝ).convolutionExists_right
      (L.precompR E) hg
        (hκ.continuous_fderiv (by simp)) x
  have hfirst : Integrable
      (fun t : E => g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ)) μ := by
    have h := hint.apply_continuousLinearMap v₀
    apply h.congr
    filter_upwards [] with t
    simp [L, complexRealMultiplication,
      ContinuousLinearMap.precompR_apply,
      Complex.real_smul, mul_comm]
  have hsecond : Integrable
      (fun t : E => g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) μ := by
    have h := hint.apply_continuousLinearMap v₁
    apply h.congr
    filter_upwards [] with t
    simp [L, complexRealMultiplication,
      ContinuousLinearMap.precompR_apply,
      Complex.real_smul, mul_comm]
  have hsplit :
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) ∂μ) =
        (∫ t : E, g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ) ∂μ) +
          Complex.I *
            (∫ t : E, g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ) ∂μ) := by
    calc
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) ∂μ) =
        ∫ t : E,
          g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I *
              (g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) ∂μ := by
            congr 1
            funext t
            ring
      _ = _ := by
        rw [integral_add hfirst (hsecond.const_mul Complex.I),
          integral_const_mul]
  unfold barPartialCoordinate
  rw [hderiv.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint v₀,
    ContinuousLinearMap.integral_apply hint v₁]
  have hgoal :
      (∫ t : E,
        (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ) =
        (2 : ℂ) *
          (∫ t : E, G j t * (κ (x - t) : ℂ) ∂μ) := by
    simpa [L, complexRealMultiplication,
      Complex.real_smul, mul_comm] using
      (hsplit.symm.trans hpositive)
  change
    ((∫ t : E,
      (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ)) / 2 =
      (G j ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) x
  rw [hgoal, MeasureTheory.convolution_def]
  simp [E, μ, complexRealMultiplication_apply, mul_comm]
end Ehrhart.TorusWeakDolbeaultMollification
