-- Prove2me | solution 1 for AvramDividend.Classical.levy_psi_affine_drift_reciprocal_tendsto_zero_ws01f
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T23:07:38.183591+00:00
-- url     : https://prove2.me/submissions/f3e72411-a55c-433c-83d2-c3ae845961c4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_reciprocal_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Topology
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hjump : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (φ C q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun β : ℝ =>
      (φ + β) / (X.ψ (φ + β) - C * (φ + β) - q))
      atTop (𝓝 0) := by
  have hnbv : ¬ X.BoundedVariation := by
    intro h
    change X.σ = 0 ∧
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) < ⊤ at h
    exact (ne_top_of_lt h.2) hjump
  have hRec :
      Tendsto (fun θ : ℝ => θ / (X.ψ θ - q)) atTop (𝓝 0) :=
    unbounded_psi_discount_reciprocal_tendsto_zero X hnbv q hq
  obtain ⟨B₁, hB₁, hlin₁⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv q hq 0
  obtain ⟨B₂, hB₂, hlin₂⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv q hq (C + 1)
  have hNz₁ : ∀ᶠ θ : ℝ in atTop, X.ψ θ - q ≠ 0 := by
    refine Filter.eventually_atTop.2 ⟨B₁, ?_⟩
    intro θ hθ
    have hh := hlin₁ θ hθ
    exact ne_of_gt (by nlinarith)
  have hNz₂ : ∀ᶠ θ : ℝ in atTop,
      X.ψ θ - C * θ - q ≠ 0 := by
    refine Filter.eventually_atTop.2 ⟨B₂, ?_⟩
    intro θ hθ
    have hh := hlin₂ θ hθ
    have hθ₁ : (1 : ℝ) ≤ θ := le_trans hB₂ hθ
    exact ne_of_gt (by nlinarith)
  have hCont : ContinuousAt (fun r : ℝ => r / (1 - C * r)) 0 := by
    have hnum : ContinuousAt (fun r : ℝ => r) 0 := continuousAt_id
    have hden : ContinuousAt (fun r : ℝ => 1 - C * r) 0 :=
      continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
    exact hnum.div₀ hden (by norm_num)
  have hTrans : Tendsto (fun θ : ℝ =>
      (θ / (X.ψ θ - q)) /
        (1 - C * (θ / (X.ψ θ - q)))) atTop (𝓝 0) := by
    change Tendsto ((fun r : ℝ => r / (1 - C * r)) ∘
      (fun θ : ℝ => θ / (X.ψ θ - q))) atTop (𝓝 0)
    simpa only [mul_zero, sub_zero, div_one, zero_div] using
      hCont.tendsto.comp hRec
  have hEq : ∀ᶠ θ : ℝ in atTop,
      (θ / (X.ψ θ - q)) /
        (1 - C * (θ / (X.ψ θ - q))) =
      θ / (X.ψ θ - C * θ - q) := by
    filter_upwards [hNz₁, hNz₂] with θ h₁ h₂
    have h₃ : 1 - C * (θ / (X.ψ θ - q)) ≠ 0 := by
      intro he
      have ha := congrArg (fun z : ℝ => z * (X.ψ θ - q)) he
      have hb : (1 - C * (θ / (X.ψ θ - q))) *
          (X.ψ θ - q) = X.ψ θ - C * θ - q := by
        field_simp [h₁] <;> ring
      rw [hb, zero_mul] at ha
      exact h₂ ha
    field_simp [h₁, h₂, h₃] <;> ring
  have hBase : Tendsto (fun θ : ℝ =>
      θ / (X.ψ θ - C * θ - q)) atTop (𝓝 0) :=
    hTrans.congr' hEq
  have hShift : Tendsto (fun β : ℝ => φ + β) atTop atTop := by
    refine Filter.tendsto_atTop.2 (fun b => ?_)
    exact Filter.eventually_atTop.2 ⟨b - φ, by
      intro β hβ
      linarith⟩
  exact hBase.comp hShift
