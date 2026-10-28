-- Prove2me | solution 1 for AvramDividend.Classical.bv_psi_two_discounts_common_tail_ws01b
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T13:21:00.802885+00:00
-- url     : https://prove2.me/submissions/8a7bf256-062e-4e9d-a26f-f8386233fcd6

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_bv_exponent_gap_div_tendsto_zero
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Order.Filter.Tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter
open scoped NNReal ENNReal

/-- A standing bounded-variation Lévy exponent eventually exceeds two discounts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q₁ q₂ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ θ : ℝ, b < θ →
      0 ≤ θ ∧ q₁ < X.ψ θ ∧ q₂ < X.ψ θ := by
  have hd : 0 < X.drift := by
    by_contra h
    exact hX.1 ⟨hBV, Or.inl (le_of_not_gt h)⟩
  have hsmall : ∀ᶠ θ : ℝ in atTop,
      (X.drift * θ - X.ψ θ) / θ < X.drift / 2 :=
    (bv_exponent_gap_div_tendsto_zero X hBV).eventually
      (eventually_lt_nhds (half_pos hd))
  obtain ⟨β, hβ⟩ := Filter.eventually_atTop.1 hsmall
  let Q : ℝ := max q₁ q₂
  let T : ℝ := 2 * (Q + 1) / X.drift
  refine ⟨max 1 (max β T), ?_, ?_⟩
  · have h := le_max_left (1 : ℝ) (max β T)
    linarith
  intro θ hθ
  have hθpos : 0 < θ := by
    have h := le_max_left (1 : ℝ) (max β T)
    linarith
  have hβθ : β ≤ θ := by
    have h₁ := le_max_left β T
    have h₂ := le_max_right (1 : ℝ) (max β T)
    linarith
  have hTθ : T < θ := by
    have h₁ := le_max_right β T
    have h₂ := le_max_right (1 : ℝ) (max β T)
    linarith
  have hprod : 2 * (Q + 1) < X.drift * θ := by
    have hh : 2 * (Q + 1) < θ * X.drift :=
      (div_lt_iff₀ hd).mp hTθ
    nlinarith
  have hψ : X.drift * θ - X.ψ θ < X.drift / 2 * θ :=
    (div_lt_iff₀ hθpos).mp (hβ θ hβθ)
  have hQ : Q < X.ψ θ := by nlinarith
  exact ⟨le_of_lt hθpos,
    lt_of_le_of_lt (le_max_left q₁ q₂) hQ,
    lt_of_le_of_lt (le_max_right q₁ q₂) hQ⟩
