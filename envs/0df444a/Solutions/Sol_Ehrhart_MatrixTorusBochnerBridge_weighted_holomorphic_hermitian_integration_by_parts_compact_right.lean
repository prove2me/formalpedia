-- Prove2me | solution 1 for Ehrhart.MatrixTorusBochnerBridge.weighted_holomorphic_hermitian_integration_by_parts_compact_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:17.121018+00:00
-- url     : https://prove2.me/submissions/2176159d-fbe7-40c5-a472-cd02bc753ef8

import Mathlib
import Definitions.Def_EhrhartVolumeInequality
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_weightedHolomorphicDerivative_eq_real
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_continuous_weightedRealDerivative
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_compactSupport_conj
import Theorems.Thm_Ehrhart_WeightedDolbeaultBochnerIdentity_integrable_of_continuous_compact_cover
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_weightedRealDerivative_integration_by_parts_compact_right
import Theorems.Thm_Ehrhart_MatrixTorusBochnerBridge_conj_barPartialCoordinate_eq_real_fderiv

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
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      weightedHolomorphicDerivative a F j z * conj (G z)
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * conj (barPartialCoordinate G z j)
      ∂(coverWeightedMeasure a)) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  let Gc : E → ℂ := fun z => conj (G z)
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hGc : ContDiff ℝ 1 Gc :=
    Complex.conjCLE.contDiff.comp hG
  have hGccompact : HasCompactSupport Gc :=
    compactSupport_conj hGcompact
  have hL₀ : Integrable
      (fun z : E => weightedRealDerivative a F v₀ z * Gc z) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_weightedRealDerivative ha hF v₀).mul
        hGc.continuous)
    exact hGccompact.mul_left
  have hL₁ : Integrable
      (fun z : E => weightedRealDerivative a F v₁ z * Gc z) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      ((continuous_weightedRealDerivative ha hF v₁).mul
        hGc.continuous)
    exact hGccompact.mul_left
  have hR₀ : Integrable
      (fun z : E => F z * (fderiv ℝ Gc z) v₀) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      (hF.continuous.mul
        ((hGc.continuous_fderiv (by simp)).clm_apply
          continuous_const))
    exact (hGccompact.fderiv_apply ℝ v₀).mul_left
  have hR₁ : Integrable
      (fun z : E => F z * (fderiv ℝ Gc z) v₁) μ := by
    apply integrable_of_continuous_compact_cover ha.continuous
      (hF.continuous.mul
        ((hGc.continuous_fderiv (by simp)).clm_apply
          continuous_const))
    exact (hGccompact.fderiv_apply ℝ v₁).mul_left
  have hLI :
      (∫ z : E,
        Complex.I * (weightedRealDerivative a F v₁ z * Gc z) ∂μ) =
      Complex.I *
        (∫ z : E,
          weightedRealDerivative a F v₁ z * Gc z ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I
      (fun z : E => weightedRealDerivative a F v₁ z * Gc z)
  have hRI :
      (∫ z : E,
        Complex.I * (F z * (fderiv ℝ Gc z) v₁) ∂μ) =
      Complex.I *
        (∫ z : E, F z * (fderiv ℝ Gc z) v₁ ∂μ) :=
    MeasureTheory.integral_const_mul Complex.I
      (fun z : E => F z * (fderiv ℝ Gc z) v₁)
  have hleft :
      (∫ z : E,
        weightedHolomorphicDerivative a F j z * Gc z ∂μ) =
      ((∫ z : E,
        weightedRealDerivative a F v₀ z * Gc z ∂μ) -
        Complex.I *
          (∫ z : E,
            weightedRealDerivative a F v₁ z * Gc z ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        (weightedRealDerivative a F v₀ z * Gc z -
          Complex.I *
            (weightedRealDerivative a F v₁ z * Gc z)) / 2
          ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [weightedHolomorphicDerivative_eq_real ha z j]
        change
          ((weightedRealDerivative a F v₀ z -
            Complex.I * weightedRealDerivative a F v₁ z) / 2) *
              Gc z = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_sub hL₀
            (hL₁.const_mul Complex.I), hLI]
  have hright :
      (∫ z : E,
        F z * conj (barPartialCoordinate G z j) ∂μ) =
      ((∫ z : E, F z * (fderiv ℝ Gc z) v₀ ∂μ) -
        Complex.I *
          (∫ z : E, F z * (fderiv ℝ Gc z) v₁ ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        (F z * (fderiv ℝ Gc z) v₀ -
          Complex.I *
            (F z * (fderiv ℝ Gc z) v₁)) / 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [conj_barPartialCoordinate_eq_real_fderiv hG z j]
        change
          F z *
            (((fderiv ℝ Gc z) v₀ -
              Complex.I * (fderiv ℝ Gc z) v₁) / 2) = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_sub hR₀
            (hR₁.const_mul Complex.I), hRI]
  have hb₀ :=
    weightedRealDerivative_integration_by_parts_compact_right
      ha hF hGc hGccompact v₀
  have hb₁ :=
    weightedRealDerivative_integration_by_parts_compact_right
      ha hF hGc hGccompact v₁
  change
    (∫ z : E,
      weightedHolomorphicDerivative a F j z * Gc z ∂μ) =
      -(∫ z : E,
        F z * conj (barPartialCoordinate G z j) ∂μ)
  calc
    _ = ((∫ z : E,
        weightedRealDerivative a F v₀ z * Gc z ∂μ) -
        Complex.I *
          (∫ z : E,
            weightedRealDerivative a F v₁ z * Gc z ∂μ)) / 2 := hleft
    _ = -(((∫ z : E, F z * (fderiv ℝ Gc z) v₀ ∂μ) -
        Complex.I *
          (∫ z : E, F z * (fderiv ℝ Gc z) v₁ ∂μ)) / 2) := by
      rw [hb₀, hb₁]
      ring
    _ = _ := congrArg Neg.neg hright.symm
end Ehrhart.MatrixTorusBochnerBridge
