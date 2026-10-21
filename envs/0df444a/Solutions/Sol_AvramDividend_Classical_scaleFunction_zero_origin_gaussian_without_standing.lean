-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_zero_origin_gaussian_without_standing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T16:00:51.687994+00:00
-- url     : https://prove2.me/submissions/ea6820af-63dc-470d-af55-4044d9eae988

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_psi_quadratic_lower_from_compensated_negative_jumps
import Theorems.Thm_AvramDividend_Classical_laplace_origin_zero_of_normalised_small
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A Gaussian q-scale function has zero value at the origin even without Standing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) : W 0 = 0 := by
  let M : ℝ := ∫ y in Iic (-1 : ℝ), (1 : ℝ) ∂X.ν
  have hM : 0 ≤ M := by
    dsimp [M]
    apply integral_nonneg
    intro y
    norm_num
  let a : ℝ := X.σ ^ 2 / 4
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hMq : 0 ≤ M + q := add_nonneg hM (le_of_lt hq)
  let K : ℝ := |X.c| + M + q
  let β : ℝ := max 1 (K / a) + 1
  have hquad : ∀ θ : ℝ, β ≤ θ →
      a * θ ^ 2 ≤ X.ψ θ - q := by
    intro θ hβ
    have hθ1 : 1 ≤ θ := by
      have hmax := le_max_left (1 : ℝ) (K / a)
      dsimp [β] at hβ
      linarith
    have hθ0 : 0 ≤ θ := by linarith
    have hθK : K / a ≤ θ := by
      have hmax := le_max_right (1 : ℝ) (K / a)
      dsimp [β] at hβ
      linarith
    have hmult := mul_le_mul_of_nonneg_left hθK (le_of_lt ha)
    have hcancel : a * (K / a) = K := by
      field_simp [ne_of_gt ha]
    have hK : K ≤ a * θ := by nlinarith [hmult]
    have hKt : K * θ ≤ a * θ ^ 2 := by
      have h := mul_le_mul_of_nonneg_right hK hθ0
      nlinarith
    have hc : 0 ≤ (|X.c| + X.c) * θ := by
      have hcc : 0 ≤ |X.c| + X.c := by
        have hh := neg_le_abs X.c
        linarith
      exact mul_nonneg hcc hθ0
    have hmqθ : 0 ≤ (M + q) * (θ - 1) := by
      apply mul_nonneg hMq
      linarith
    have hessential : -X.c * θ + M + q ≤ a * θ ^ 2 := by
      dsimp [K] at hKt
      nlinarith [hKt, hc, hmqθ]
    have hpsi := psi_quadratic_lower_from_compensated_negative_jumps X θ hθ0
    dsimp [a, M] at hessential ⊢
    nlinarith [hpsi, hessential]
  apply laplace_origin_zero_of_normalised_small W X.ψ q β
    hW.2.1 hW.2.2.2.1
  · intro θ hβ hθ
    have hpos : 0 < a * θ ^ 2 := by positivity
    have hψ : q < X.ψ θ := by
      have hh := hquad θ hβ
      linarith
    -- The Laplace identity of the scale function is stated with the discount
    -- factor `Real.exp (-(θ * y))`, while the origin criterion uses the
    -- factor `Real.exp (-θ * x)`; the two differ only by the parenthesisation
    -- of the exponent, which the ring identity settles.
    obtain ⟨hint, hval⟩ := hW.2.2.2.2 θ (le_of_lt hθ) hψ
    have hbridge : (fun x : ℝ => Real.exp (-(θ * x)) * W x) =
        (fun x : ℝ => Real.exp (-θ * x) * W x) := by
      funext x
      congr 1
      ring
    rw [← hbridge]
    exact ⟨hint, hval⟩
  · intro ε hε
    let t : ℝ := a * ε
    have ht : 0 < t := mul_pos ha hε
    let θ : ℝ := max β (max 1 t⁻¹) + 1
    have hβ : β ≤ θ := by
      have hm := le_max_left β (max 1 t⁻¹)
      dsimp [θ]
      linarith
    have hθ : 0 < θ := by
      have hm₁ := le_max_left (1 : ℝ) t⁻¹
      have hm₂ := le_max_right β (max 1 t⁻¹)
      dsimp [θ]
      linarith
    have hi : t⁻¹ < θ := by
      have hm₁ := le_max_right (1 : ℝ) t⁻¹
      have hm₂ := le_max_right β (max 1 t⁻¹)
      dsimp [θ]
      linarith
    have hlarge : 1 < t * θ := by
      calc
        1 = t * t⁻¹ := (mul_inv_cancel₀ (ne_of_gt ht)).symm
        _ < t * θ := mul_lt_mul_of_pos_left hi ht
    have hineq : θ < ε * (a * θ ^ 2) := by
      calc
        θ = (1 : ℝ) * θ := by ring
        _ < (t * θ) * θ := mul_lt_mul_of_pos_right hlarge hθ
        _ = ε * (a * θ ^ 2) := by dsimp [t]; ring
    have hqbound := hquad θ hβ
    have hden : 0 < X.ψ θ - q := by
      have hpos : 0 < a * θ ^ 2 := by positivity
      linarith
    refine ⟨θ, hβ, hθ, ?_⟩
    change θ / (X.ψ θ - q) < ε
    apply (div_lt_iff₀ hden).2
    exact lt_of_lt_of_le hineq
      (mul_le_mul_of_nonneg_left hqbound (le_of_lt hε))
