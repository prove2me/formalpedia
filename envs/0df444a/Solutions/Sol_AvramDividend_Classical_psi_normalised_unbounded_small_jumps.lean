-- Prove2me | solution 1 for AvramDividend.Classical.psi_normalised_unbounded_small_jumps
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:49:30.773655+00:00
-- url     : https://prove2.me/submissions/826c5aac-a658-4577-820b-e8a12845556b

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Positivity
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_small_negative_compensated_div_integrable
import Theorems.Thm_AvramDividend_Classical_levy_large_negative_jump_unit_integrable
import Theorems.Thm_AvramDividend_Classical_negative_compensated_real_integral_tendsto_atTop
import Theorems.Thm_AvramDividend_Classical_negative_compensated_integral_mono
import Theorems.Thm_AvramDividend_Classical_psi_normalised_lower_bound_small

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Infinite small-jump first moment gives arbitrarily large normalised exponent tails. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ := by
  intro C
  let s : Set ℝ := Ioo (-1 : ℝ) 0
  let μ : Measure ℝ := X.ν.restrict s
  let J : ℝ → ℝ := fun θ =>
    ∫ y : ℝ, (Real.exp (θ * y) - 1 - θ * y) / θ ∂μ
  let B : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  have hneg : ∀ᵐ y ∂μ, y < 0 := by
    dsimp [μ, s]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun y hy => hy.2)
  have hint : ∀ θ : ℝ, 0 < θ →
      Integrable (fun y : ℝ =>
        (Real.exp (θ * y) - 1 - θ * y) / θ) μ := by
    intro θ hθ
    simpa only [μ, s, IntegrableOn] using
      (levy_small_negative_compensated_div_integrable X θ hθ)
  have hinfμ : (∫⁻ y : ℝ, ENNReal.ofReal |y| ∂μ) = ⊤ := by
    simpa only [μ, s] using hinf
  have hJlim : Tendsto (fun n : ℕ => J ((n : ℝ) + 1))
      atTop atTop := by
    have hlim :=
      negative_compensated_real_integral_tendsto_atTop μ hneg hinfμ
        (fun n => hint ((n : ℝ) + 1) (by positivity))
    simpa only [J] using hlim
  have hJmono : ∀ θ₁ θ₂ : ℝ, 0 < θ₁ → θ₁ ≤ θ₂ →
      J θ₁ ≤ J θ₂ := by
    intro θ₁ θ₂ hθ₁ hθ
    have hθ₂ : 0 < θ₂ := lt_of_lt_of_le hθ₁ hθ
    exact negative_compensated_integral_mono μ θ₁ θ₂ hθ₁ hθ hneg
      (hint θ₁ hθ₁) (hint θ₂ hθ₂)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact integral_nonneg (fun _ => zero_le_one)
  have hJeve : ∀ᶠ n : ℕ in atTop,
      C - X.c + B + 1 < J ((n : ℝ) + 1) :=
    hJlim.eventually (eventually_gt_atTop (C - X.c + B + 1))
  rcases (eventually_atTop.1 hJeve) with ⟨N, hN⟩
  refine ⟨(N : ℝ) + 1, by
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    linarith, ?_⟩
  intro θ hNθ
  have hNpos : 0 < (N : ℝ) + 1 := by positivity
  have hθpos : 0 < θ := lt_of_lt_of_le hNpos hNθ
  have hθone : 1 ≤ θ := by
    have hNnonneg : 0 ≤ (N : ℝ) := by positivity
    linarith
  have hJθ : J ((N : ℝ) + 1) ≤ J θ :=
    hJmono ((N : ℝ) + 1) θ hNpos hNθ
  have hBθ : B / θ ≤ B := by
    apply (div_le_iff₀ hθpos).2
    calc
      B = B * 1 := by ring
      _ ≤ B * θ := mul_le_mul_of_nonneg_left hθone hB
  have hbig : C < X.c + J θ - B / θ := by
    have hJN := hN N le_rfl
    linarith
  have hlarge := levy_large_negative_jump_unit_integrable X
  have hlower := psi_normalised_lower_bound_small X hσ θ hθpos hlarge
  have hJeq :
      J θ =
        (∫ y in Ioo (-1 : ℝ) 0,
          (Real.exp (θ * y) - 1 - θ * y) ∂X.ν) / θ := by
    dsimp [J, μ, s]
    exact integral_div θ
      (fun y : ℝ => Real.exp (θ * y) - 1 - θ * y)
  have hnorm :
      X.c + J θ - B / θ ≤ X.ψ θ / θ := by
    simpa only [B, hJeq] using hlower
  exact lt_of_lt_of_le hbig hnorm
