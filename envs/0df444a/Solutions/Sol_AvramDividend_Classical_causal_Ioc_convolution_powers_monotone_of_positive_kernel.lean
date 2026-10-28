-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_convolution_powers_monotone_of_positive_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:33:01.786651+00:00
-- url     : https://prove2.me/submissions/964ea2f4-dbbf-4b6b-a083-8723498447dc

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_continuous_product_integrable_full
import Theorems.Thm_AvramDividend_Classical_full_convolution_powers_monotone_of_nonnegative_kernel
import Mathlib.Order.Monotone.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- Positive-interval convolution powers of a monotone causal kernel remain monotone. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκmono : Monotone κ)
    (hκpos : ∀ x : ℝ, 0 ≤ κ x)
    (hFcont : ∀ n : ℕ, Continuous (F n))
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Monotone (F n) := by
  obtain ⟨hFzero, hFfull⟩ :=
    causal_Ioc_convolution_powers_full_real_recursion
      κ F hκzero hF0 hFsucc
  have hInt : ∀ n : ℕ, ∀ x : ℝ,
      Integrable (fun y : ℝ => κ y * F n (x - y)) volume := by
    intro n x
    exact causal_continuous_product_integrable_full
      κ (F n) hκcont (hFcont n)
      (fun y hy => hκzero y hy.le)
      (fun y hy => hFzero n y hy.le) x
  exact full_convolution_powers_monotone_of_nonnegative_kernel
    κ F hκmono hκpos hF0 hFfull hInt
