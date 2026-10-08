-- Prove2me | solution 1 for AvramDividend.Classical.excursion_killed_ladder_potential_full_support_from_laplace_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:19:38.655203+00:00
-- url     : https://prove2.me/submissions/1a2fe412-6651-4e6c-ad47-e0c09a4631f8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_excursion_zero_cumulative_mass_implies_ae_support_gap
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_upper_bound_from_support_gap
import Theorems.Thm_AvramDividend_Classical_excursion_inverse_laplace_lower_bound_excludes_exponential_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (β : Measure ℝ) [IsFiniteMeasure β] (c : ℝ) (hc : 0 < c)
    (hint : ∀ θ : ℝ, 0 < θ →
      Integrable (fun y : ℝ => Real.exp (-(θ * y))) β)
    (hlower : ∀ θ : ℝ, 0 < θ →
      c / θ ≤ ∫ y : ℝ, Real.exp (-(θ * y)) ∂β) :
    ∀ x : ℝ, 0 < x → 0 < β (Iic x) := by
  intro x hx
  by_contra hnot
  have hzero : β (Iic x) = 0 :=
    le_antisymm (le_of_not_gt hnot) bot_le
  have hsupport : ∀ᵐ y : ℝ ∂β, x ≤ y :=
    (excursion_zero_cumulative_mass_implies_ae_support_gap β x hzero).mono
      (fun y hy => le_of_lt hy)
  have hC : 0 ≤ β.real univ := ENNReal.toReal_nonneg
  have henvelope : ∀ θ : ℝ, 0 < θ →
      c / θ ≤ β.real univ * Real.exp (-(θ * x)) := by
    intro θ hθ
    exact (hlower θ hθ).trans
      (excursion_laplace_upper_bound_from_support_gap
        β x θ hθ.le hsupport (hint θ hθ))
  exact excursion_inverse_laplace_lower_bound_excludes_exponential_envelope
    c (β.real univ) x hc hC hx henvelope
