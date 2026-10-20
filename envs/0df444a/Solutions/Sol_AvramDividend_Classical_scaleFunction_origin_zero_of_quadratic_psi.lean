-- Prove2me | solution 1 for AvramDividend.Classical.scaleFunction_origin_zero_of_quadratic_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:33:22.919805+00:00
-- url     : https://prove2.me/submissions/fe9d2385-e672-491b-bf88-1db9f429f9fc

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_laplace_origin_zero_of_normalised_small
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- An eventual positive quadratic lower bound on the exponent implies W(0)=0. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q a β : ℝ) (ha : 0 < a)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hquad : ∀ θ : ℝ, β ≤ θ → a * θ ^ 2 ≤ X.ψ θ - q) :
    W 0 = 0 := by
  apply laplace_origin_zero_of_normalised_small W X.ψ q β
    hW.2.1 hW.2.2.2.1
  · intro θ hβ hθ
    have hpos : 0 < a * θ ^ 2 := by positivity
    have hψ : q < X.ψ θ := by
      have hbound := hquad θ hβ
      linarith
    simpa only [neg_mul] using (hW.2.2.2.2 θ (le_of_lt hθ) hψ)
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
    have hq := hquad θ hβ
    have hden : 0 < X.ψ θ - q := by
      have hpos : 0 < a * θ ^ 2 := by positivity
      linarith
    refine ⟨θ, hβ, hθ, ?_⟩
    change θ / (X.ψ θ - q) < ε
    apply (div_lt_iff₀ hden).2
    exact lt_of_lt_of_le hineq (mul_le_mul_of_nonneg_left hq (le_of_lt hε))
