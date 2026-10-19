-- Prove2me | solution 1 for Ehrhart.DolbeaultRegularity.weak_barPartial_convolution_barPartial_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:13.178776+00:00
-- url     : https://prove2.me/submissions/9cf790f3-2209-4efa-aaec-1dd17e109d22

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
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
open Ehrhart.DolbeaultRegularity
open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution
namespace Ehrhart.DolbeaultRegularity
theorem _root_.solution {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0))
    (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      x j = 0 := by
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
          ∂μ) = 0 := by
    simpa only [E, μ, v₀, v₁,
      translatedRealKernel_fderiv hκ x,
      Complex.ofReal_neg, mul_neg, ← neg_add] using htest
  have hzero :
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ))
          ∂μ) = 0 := by
    simpa only [integral_neg, neg_eq_zero] using hnegative
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
  change
    ((∫ t : E,
      (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ)) / 2 = 0
  have hgoal :
      (∫ t : E,
        (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ) = 0 := by
    simpa [L, complexRealMultiplication,
      Complex.real_smul, mul_comm] using
      (hsplit.symm.trans hzero)
  rw [hgoal]
  simp
end Ehrhart.DolbeaultRegularity
