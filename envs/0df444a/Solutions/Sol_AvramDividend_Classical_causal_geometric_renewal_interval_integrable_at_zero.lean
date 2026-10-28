-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_renewal_interval_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:19:28.844981+00:00
-- url     : https://prove2.me/submissions/e5c4d835-e947-48c7-8c02-0e1add3a19ba

import Theorems.Thm_AvramDividend_Classical_nonnegative_geometric_renewal_interval_integrable_at_zero
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Causality reduces positivity and series convergence to positive times. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume)
    (hzero : ∀ n : ℕ, ∀ x : ℝ, x ≤ 0 → F n x = 0)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 < x → 0 ≤ F n x)
    (hpoint : ∀ x : ℝ, 0 < x →
      Summable (fun n : ℕ => F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) ≤ ρ ^ (n + 1)) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x := by
  have hposAll (n : ℕ) (x : ℝ) : 0 ≤ F n x := by
    by_cases hx : 0 < x
    · exact hpos n x hx
    · rw [hzero n x (le_of_not_gt hx)]
  have hsumAll (x : ℝ) : Summable (fun n : ℕ => F n x) := by
    by_cases hx : 0 < x
    · exact hpoint x hx
    · have hz : (fun n : ℕ => F n x) = (fun _ => (0 : ℝ)) := by
        funext n
        exact hzero n x (le_of_not_gt hx)
      rw [hz]
      exact summable_zero
  exact nonnegative_geometric_renewal_interval_integrable_at_zero
    F ρ hρnonneg hρlt hFi hposAll hsumAll hmass
