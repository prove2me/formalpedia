-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_psi_discount_reciprocal_small
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:59:31.582846+00:00
-- url     : https://prove2.me/submissions/9b4b7687-960a-4b2a-9253-97fb5c1b709c

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For unbounded variation the discounted inverse Laplace denominator, after
normalisation by θ, becomes arbitrarily small at large positive arguments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ β : ℝ, 1 ≤ β ∧
        ∀ θ : ℝ, β ≤ θ →
          0 ≤ θ / (X.ψ θ - q) ∧
            θ / (X.ψ θ - q) < ε := by
  intro ε hε
  obtain ⟨β, hβ, hlinear⟩ :=
    unbounded_psi_discount_denominator_eventually_linear X hnbv q hq ε⁻¹
  refine ⟨β, hβ, ?_⟩
  intro θ hθ
  have hθone : 1 ≤ θ := le_trans hβ hθ
  have hθpos : 0 < θ := lt_of_lt_of_le zero_lt_one hθone
  have hbound := hlinear θ hθ
  have hdenpos : 0 < X.ψ θ - q := by
    have hinvpos : 0 < ε⁻¹ := inv_pos.mpr hε
    have hmul : 0 < ε⁻¹ * θ := mul_pos hinvpos hθpos
    linarith
  constructor
  · exact div_nonneg hθpos.le hdenpos.le
  · apply (div_lt_iff₀ hdenpos).2
    calc
      θ = ε * (ε⁻¹ * θ) := by field_simp
      _ < ε * (X.ψ θ - q) := by
        apply mul_lt_mul_of_pos_left ?_ hε
        linarith
