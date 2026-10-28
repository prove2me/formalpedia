-- Prove2me | solution 1 for AvramDividend.Classical.causal_convolution_powers_continuous_of_bounded_kernel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:17:48.077217+00:00
-- url     : https://prove2.me/submissions/f8d579ac-db3a-46b5-bede-965db47bbc36

import Theorems.Thm_AvramDividend_Classical_continuous_causal_convolution_of_bounded_continuous_left
import Mathlib.Order.Bounds.Defs
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A bounded continuous causal renewal kernel has continuous L1 convolution powers. -/
theorem solution
    (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hκc : Continuous κ)
    (hκb : BddAbove (Set.range fun x : ℝ => ‖κ x‖))
    (hFi : ∀ n : ℕ, Integrable (F n) volume)
    (hF0 : F 0 = κ)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Continuous (F n) := by
  intro n
  cases n with
  | zero => simpa [hF0] using hκc
  | succ n =>
      rw [hFsucc n]
      exact continuous_causal_convolution_of_bounded_continuous_left
        κ (F n) hκc hκb (hFi n)
