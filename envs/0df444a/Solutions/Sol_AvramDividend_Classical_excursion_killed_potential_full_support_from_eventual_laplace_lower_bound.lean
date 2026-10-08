-- Prove2me | solution 1 for AvramDividend.Classical.excursion_killed_potential_full_support_from_eventual_laplace_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T07:33:02.418366+00:00
-- url     : https://prove2.me/submissions/864b4202-9435-459e-9e32-d41c73cc0b7e

import Mathlib
import Theorems.Thm_AvramDividend_Classical_excursion_zero_cumulative_mass_implies_ae_support_gap
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_upper_bound_from_support_gap
import Theorems.Thm_AvramDividend_Classical_excursion_laplace_exponential_beats_inverse_above_one

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (β : Measure ℝ) [IsFiniteMeasure β] (c : ℝ) (hc : 0 < c)
    (hint : ∀ θ : ℝ, 1 ≤ θ →
      Integrable (fun y : ℝ => Real.exp (-(θ * y))) β)
    (hlower : ∀ θ : ℝ, 1 ≤ θ →
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
  have hCpos : 0 < β.real univ + 1 := by linarith
  obtain ⟨θ, hθ, hsmall⟩ :=
    excursion_laplace_exponential_beats_inverse_above_one
      (c / (β.real univ + 1)) x (div_pos hc hCpos) hx
  have hθpos : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
  have henv : c / θ ≤ β.real univ * Real.exp (-(θ * x)) :=
    (hlower θ hθ).trans
      (excursion_laplace_upper_bound_from_support_gap
        β x θ hθpos.le hsupport (hint θ hθ))
  have hlower' : c ≤
      (β.real univ * Real.exp (-(θ * x))) * θ :=
    (div_le_iff₀ hθpos).mp henv
  have hnonneg : 0 ≤ θ * Real.exp (-(θ * x)) :=
    (mul_pos hθpos (Real.exp_pos _)).le
  have hupper : β.real univ * (θ * Real.exp (-(θ * x))) ≤
      (β.real univ + 1) * (θ * Real.exp (-(θ * x))) :=
    mul_le_mul_of_nonneg_right (by linarith) hnonneg
  have hstrict :
      (β.real univ + 1) * (θ * Real.exp (-(θ * x))) < c := by
    have htmp := (lt_div_iff₀ hCpos).mp hsmall
    nlinarith
  nlinarith [hlower', hupper, hstrict]
