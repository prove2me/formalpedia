-- Prove2me | solution 1 for AvramDividend.Classical.real_convolution_power_recursion_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T22:42:41.333222+00:00
-- url     : https://prove2.me/submissions/741dc066-c5f2-42a1-a7e3-c99339e1183e

import Mathlib.MeasureTheory.Integral.Prod

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The pointwise real convolution recursion preserves measurability of every power. -/
theorem solution
    (k : ℝ → ℝ) (F : ℕ → ℝ → ℝ)
    (hk : Measurable k)
    (hFzero : F 0 = k)
    (hFsucc : ∀ n : ℕ, F (n + 1) =
      fun x : ℝ => ∫ y : ℝ, k y * F n (x - y) ∂volume) :
    ∀ n : ℕ, Measurable (F n) := by
  intro n
  induction n with
  | zero =>
      simpa only [hFzero] using hk
  | succ n ih =>
      rw [hFsucc n]
      have hprod : Measurable (fun p : ℝ × ℝ =>
          k p.2 * F n (p.1 - p.2)) :=
        (hk.comp measurable_snd).mul
          (ih.comp (measurable_fst.sub measurable_snd))
      exact (hprod.stronglyMeasurable.integral_prod_right').measurable
