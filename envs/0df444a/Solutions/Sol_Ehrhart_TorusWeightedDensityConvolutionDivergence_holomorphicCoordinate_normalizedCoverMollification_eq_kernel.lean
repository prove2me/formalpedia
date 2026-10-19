-- Prove2me | solution 1 for Ehrhart.TorusWeightedDensityConvolutionDivergence.holomorphicCoordinate_normalizedCoverMollification_eq_kernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:21.159885+00:00
-- url     : https://prove2.me/submissions/6e79e4b7-a1e4-49c3-be0b-aab0b34302cd

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_DolbeaultRegularity_complexRealMultiplication_apply
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_contDiff
import Theorems.Thm_Ehrhart_DolbeaultRegularity_translatedRealKernel_fderiv

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] _p2m_local_instance_3610026555_5
noncomputable section
open Ehrhart
open Set MeasureTheory
open scoped BigOperators ENNReal
open Ehrhart.TorusWeightedDensityConvolutionDivergence
open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters DolbeaultRegularity
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution
namespace Ehrhart.TorusWeightedDensityConvolutionDivergence
theorem _root_.solution
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : LocallyIntegrable g (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) (j : Fin n) :
    holomorphicCoordinate (normalizedCoverMollification g k) x j =
      -(∫ y : LogSpace n,
        g y *
          conj (barPartialCoordinate
            (fun z : LogSpace n =>
              ((complexShrinkingBump (n := n) k).normed
                (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j)
        ∂(volume : Measure (LogSpace n))) := by
  let E := LogSpace n
  let μ : Measure E := volume
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := complexRealMultiplication
  let κ : E → ℝ :=
    (complexShrinkingBump (n := n) k).normed μ
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
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
  have htranslated :
      Differentiable ℝ (fun t : E => κ (x - t)) :=
    (translatedRealKernel_contDiff hκ x).differentiable (by simp)
  have hkernel (y : E) :
      conj (barPartialCoordinate
        (fun z : E => (κ (x - z) : ℂ)) y j) =
      -((((fderiv ℝ κ (x - y)) v₀ : ℂ) -
        Complex.I * ((fderiv ℝ κ (x - y)) v₁ : ℂ)) / 2) := by
    unfold barPartialCoordinate
    rw [fderiv_complexOfReal htranslated y v₀,
      fderiv_complexOfReal htranslated y v₁,
      translatedRealKernel_fderiv hκ x y v₀,
      translatedRealKernel_fderiv hκ x y v₁]
    simp [map_add, map_mul, map_ofNat,
      Complex.conj_I, Complex.ofReal_neg, div_eq_mul_inv] ; ring
  change
    holomorphicCoordinate
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x j =
      -(∫ y : E,
        g y *
          conj (barPartialCoordinate
            (fun z : E => (κ (x - z) : ℂ)) y j)
        ∂μ)
  rw [← complex_convolution_flip]
  unfold holomorphicCoordinate
  rw [hderiv.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint v₀,
    ContinuousLinearMap.integral_apply hint v₁]
  change
    ((∫ y : E,
      (L (g y)) ((fderiv ℝ κ (x - y)) v₀) ∂μ) -
      Complex.I *
        (∫ y : E,
          (L (g y)) ((fderiv ℝ κ (x - y)) v₁) ∂μ)) / 2 =
    -(∫ y : E,
      g y *
        conj (barPartialCoordinate
          (fun z : E => (κ (x - z) : ℂ)) y j)
      ∂μ)
  have hsplit :
      (∫ y : E,
        (g y * ((fderiv ℝ κ (x - y)) v₀ : ℂ) -
          Complex.I *
            (g y * ((fderiv ℝ κ (x - y)) v₁ : ℂ))) / 2
        ∂μ) =
      ((∫ y : E,
        g y * ((fderiv ℝ κ (x - y)) v₀ : ℂ) ∂μ) -
        Complex.I *
          (∫ y : E,
            g y * ((fderiv ℝ κ (x - y)) v₁ : ℂ) ∂μ)) / 2 := by
    rw [integral_div,
      integral_sub hfirst (hsecond.const_mul Complex.I),
      integral_const_mul]
  calc
    ((∫ y : E,
      (L (g y)) ((fderiv ℝ κ (x - y)) v₀) ∂μ) -
      Complex.I *
        (∫ y : E,
          (L (g y)) ((fderiv ℝ κ (x - y)) v₁) ∂μ)) / 2 =
      ∫ y : E,
        (g y * ((fderiv ℝ κ (x - y)) v₀ : ℂ) -
          Complex.I *
            (g y * ((fderiv ℝ κ (x - y)) v₁ : ℂ))) / 2
        ∂μ := by
      simpa [L, complexRealMultiplication_apply, mul_comm] using hsplit.symm
    _ = -(∫ y : E,
      g y *
        conj (barPartialCoordinate
          (fun z : E => (κ (x - z) : ℂ)) y j)
      ∂μ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hkernel y]
      ring
end Ehrhart.TorusWeightedDensityConvolutionDivergence
