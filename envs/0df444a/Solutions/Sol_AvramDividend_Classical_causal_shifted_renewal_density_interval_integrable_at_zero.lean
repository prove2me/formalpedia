-- Prove2me | solution 1 for AvramDividend.Classical.causal_shifted_renewal_density_interval_integrable_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:32:34.606515+00:00
-- url     : https://prove2.me/submissions/86ce32d9-ff9e-4555-84fb-07ef078e2133

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Theorems.Thm_AvramDividend_Classical_causal_renewal_shifted_tsum_eq_unshifted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Shifted renewal sums inherit integrability at zero, also after scaling. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (b : ℝ)
    (hpoint : ∀ y : ℝ, 0 < y → Summable (fun n : ℕ => F n y))
    (hint : ∀ x : ℝ, 0 < x →
      IntervalIntegrable (fun y : ℝ => ∑' n : ℕ, F n y) volume 0 x) :
    ∀ x : ℝ, 0 < x →
      IntervalIntegrable
        (fun y : ℝ => b * ∑' n : ℕ,
          if n = 0 then (0 : ℝ) else F (n - 1) y)
        volume 0 x := by
  intro x hx
  have hintx : IntegrableOn (fun y : ℝ => b * ∑' n : ℕ, F n y)
      (Ioc (0 : ℝ) x) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hx)).1
      ((hint x hx).const_mul b)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt hx)).2
  apply hintx.congr_fun ?_ measurableSet_Ioc
  intro y hy
  change b * (∑' n : ℕ, F n y) =
    b * (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)
  rw [causal_renewal_shifted_tsum_eq_unshifted
    (fun n : ℕ => F n y) (hpoint y hy.1)]
