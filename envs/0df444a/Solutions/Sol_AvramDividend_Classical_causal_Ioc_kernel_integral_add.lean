-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_kernel_integral_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:56:02.235514+00:00
-- url     : https://prove2.me/submissions/1abb5e01-3dcc-4dfa-b091-4b13a312e3c8

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The causal interval convolution distributes over an integrable sum. -/
theorem solution
    (B f g : ℝ → ℝ) (x : ℝ)
    (hf : IntegrableOn (fun s : ℝ => B (x - s) * f s)
      (Ioc (0 : ℝ) x) volume)
    (hg : IntegrableOn (fun s : ℝ => B (x - s) * g s)
      (Ioc (0 : ℝ) x) volume) :
    (∫ s in Ioc (0 : ℝ) x, B (x - s) * (f s + g s) ∂volume) =
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * f s ∂volume) +
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * g s ∂volume) := by
  simpa only [mul_add] using (MeasureTheory.integral_add hf hg)
