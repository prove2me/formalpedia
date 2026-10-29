-- Prove2me | solution 1 for AvramDividend.Classical.levy_genuine_descending_factor_tendsto_zero_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:23:20.544977+00:00
-- url     : https://prove2.me/submissions/221931db-b78b-4ad4-bcd1-f7196e8d143d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ q p lam : ℝ) (hqp : 0 ≤ q + p) :
    Tendsto (fun β : ℝ =>
      (p / lam) * ((lam - β) /
        (p - (X.ψ (φ + β) - q)))) atTop (𝓝 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro h
    change X.σ = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ at h
    exact (ne_top_of_lt h.2) hjump
  have hRec : Tendsto (fun β : ℝ =>
      (φ + β) / (X.ψ (φ + β) - (q + p))) atTop (𝓝 0) := by
    simpa only [zero_mul, sub_zero] using
      levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
        X hjump φ 0 (q + p) hqp
  obtain ⟨B, hB, hlin⟩ :=
    unbounded_psi_discount_denominator_eventually_linear
      X hnbv (q + p) hqp 0
  have hShift : Tendsto (fun β : ℝ => φ + β) atTop atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    exact Filter.eventually_atTop.2 ⟨b - φ, by
      intro β hβ
      linarith⟩
  have hDen : ∀ᶠ β : ℝ in atTop, X.ψ (φ + β) - (q + p) ≠ 0 := by
    have hh : ∀ᶠ β : ℝ in atTop, B ≤ φ + β :=
      hShift.eventually (Filter.eventually_ge_atTop B)
    filter_upwards [hh] with β hβ
    exact ne_of_gt (by
      have hs := hlin (φ + β) hβ
      nlinarith)
  have hShiftNz : ∀ᶠ β : ℝ in atTop, φ + β ≠ 0 := by
    have hh := hShift.eventually (Filter.eventually_gt_atTop 0)
    filter_upwards [hh] with β hβ
    exact ne_of_gt hβ
  have hInv : Tendsto (fun β : ℝ => (φ + β)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hShift
  have hCorr : Tendsto (fun β : ℝ => (φ + lam) * (φ + β)⁻¹)
      atTop (𝓝 0) := by
    convert tendsto_const_nhds.mul hInv using 1 <;> simp
  have hRatio : Tendsto (fun β : ℝ =>
      (β - lam) / (φ + β)) atTop (𝓝 1) := by
    have hs : Tendsto (fun β : ℝ =>
        1 - (φ + lam) * (φ + β)⁻¹) atTop (𝓝 1) := by
      convert tendsto_const_nhds.sub hCorr using 1 <;> simp
    apply hs.congr'
    filter_upwards [hShiftNz] with β hn
    field_simp [hn]
    ring
  have hProd : Tendsto (fun β : ℝ =>
      ((β - lam) / (φ + β)) *
        ((φ + β) / (X.ψ (φ + β) - (q + p))))
      atTop (𝓝 0) := by
    convert hRatio.mul hRec using 1 <;> simp
  have hEq : ∀ᶠ β : ℝ in atTop,
      ((β - lam) / (φ + β)) *
        ((φ + β) / (X.ψ (φ + β) - (q + p))) =
      (lam - β) / (p - (X.ψ (φ + β) - q)) := by
    filter_upwards [hShiftNz, hDen] with β h₁ h₂
    have h₃ : p - (X.ψ (φ + β) - q) ≠ 0 := by
      intro he
      apply h₂
      linarith
    field_simp [h₁, h₂, h₃] <;> ring
  have hLimit : Tendsto (fun β : ℝ =>
      (lam - β) / (p - (X.ψ (φ + β) - q)))
      atTop (𝓝 0) := hProd.congr' hEq
  convert tendsto_const_nhds.mul hLimit using 1 <;> simp
