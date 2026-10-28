-- Prove2me | solution 1 for AvramDividend.Classical.causal_renewal_truncated_primitive_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T09:55:32.291176+00:00
-- url     : https://prove2.me/submissions/ee417b4d-72be-4272-9d6f-bf66fad347d1

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_continuous_of_convolution_bounds
import Theorems.Thm_AvramDividend_Classical_causal_renewal_density_interval_integrable_away_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

/-- The cumulative positive-time renewal density has its expected derivative. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hκint : Integrable κ volume)
    (hκcont : ContinuousOn κ (Ioi (0 : ℝ)))
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκbound : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume)
    (hFnonneg : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x)
    (hFpoint : ∀ n : ℕ, ∀ x : ℝ, 0 < x →
      F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x)
    (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) :
    deriv (fun b : ℝ =>
      ∫ y in a..b, (∑' n : ℕ,
        if n = 0 then (0 : ℝ) else F (n - 1) y)) x =
      ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) x := by
  let g : ℝ → ℝ := fun y =>
    ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y
  have hcont : ContinuousOn g (Ioi (0 : ℝ)) :=
    causal_renewal_density_continuous_of_convolution_bounds
      κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound
      hF0 hFsucc hFnonneg hFpoint
  have hint : IntervalIntegrable g volume a x :=
    causal_renewal_density_interval_integrable_away_zero
      κ F ρ hρ0 hρ1 hκint hκcont hκzero hκbound
      hF0 hFsucc hFnonneg hFpoint a x ha hax
  have hx : x ∈ Ioi (0 : ℝ) := lt_of_lt_of_le ha hax
  have hmeas : StronglyMeasurableAtFilter g (nhds x) volume :=
    hcont.stronglyMeasurableAtFilter isOpen_Ioi x hx
  have hcx : ContinuousAt g x :=
    hcont.continuousAt (isOpen_Ioi.mem_nhds hx)
  exact intervalIntegral.deriv_integral_right hint hmeas hcx
