-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_convolution_powers_continuous_of_bounded_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:25:51.296987+00:00
-- url     : https://prove2.me/submissions/9bacaf22-152e-44d8-a7bf-6f22ddb0c12a

import Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_powers_full_real_recursion
import Theorems.Thm_AvramDividend_Classical_causal_positive_l1_global_integrable
import Theorems.Thm_AvramDividend_Classical_causal_convolution_powers_continuous_of_bounded_kernel
import Mathlib.Order.Bounds.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A continuous bounded causal kernel gives continuous powers even for an Ioc recursion. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκzero : ∀ x : ℝ, x ≤ 0 → κ x = 0)
    (hκcont : Continuous κ)
    (hκbdd : BddAbove (Set.range fun x : ℝ => ‖κ x‖))
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y in Ioc (0 : ℝ) x,
        κ y * F n (x - y) ∂volume)
    (hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi (0 : ℝ)) volume) :
    ∀ n : ℕ, Continuous (F n) := by
  obtain ⟨hFzero, hFfull⟩ :=
    causal_Ioc_convolution_powers_full_real_recursion
      κ F hκzero hF0 hFsucc
  have hFglobal : ∀ n : ℕ, Integrable (F n) volume := by
    intro n
    exact causal_positive_l1_global_integrable
      (F n) (hFi n) (hFzero n)
  exact causal_convolution_powers_continuous_of_bounded_kernel
    κ F hκcont hκbdd hFglobal hF0 hFfull
