-- Prove2me | solution 1 for AvramDividend.Classical.causal_Ioc_kernel_integral_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:56:05.266394+00:00
-- url     : https://prove2.me/submissions/88f55c7f-f545-4896-b408-913c15f71b1d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exchange a finite Neumann input sum with a causal interval integral. -/
theorem solution
    (B : ℝ → ℝ) (Q : ℕ → ℝ → ℝ) (x : ℝ) (n : ℕ)
    (hI : ∀ i ∈ Finset.range (n + 1),
      IntegrableOn (fun s : ℝ => B (x - s) * Q i s)
        (Ioc (0 : ℝ) x) volume) :
    (∫ s in Ioc (0 : ℝ) x,
      B (x - s) * (∑ i ∈ Finset.range (n + 1), Q i s) ∂volume) =
    ∑ i ∈ Finset.range (n + 1),
      (∫ s in Ioc (0 : ℝ) x, B (x - s) * Q i s ∂volume) := by
  classical
  simpa only [Finset.mul_sum] using
    (MeasureTheory.integral_finset_sum
      (μ := volume.restrict (Ioc (0 : ℝ) x))
      (Finset.range (n + 1)) hI)
