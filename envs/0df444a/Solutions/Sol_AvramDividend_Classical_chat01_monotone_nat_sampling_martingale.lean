-- Prove2me | solution 1 for AvramDividend.Classical.chat01_monotone_nat_sampling_martingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:06:50.690296+00:00
-- url     : https://prove2.me/submissions/1f7943c5-d203-4851-b7ae-23b3dcacc4fb

import Mathlib.Probability.Martingale.Basic
import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- Sampling a nonnegative-real-time martingale along any increasing
    sequence of times produces a discrete martingale. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → ℝ}
    (e : ℕ → ℝ≥0) (he : Monotone e) (hf : Martingale f 𝓕 μ) :
    Martingale (fun (n : ℕ) => f (e n))
      ({ seq := fun (n : ℕ) => 𝓕 (e n)
         mono' := by
           intro i j hij
           exact 𝓕.mono (he hij)
         le' := by
           intro n
           exact 𝓕.le (e n) } : Filtration ℕ mΩ) μ := by
  constructor
  · intro n
    exact hf.1 (e n)
  · intro i j hij
    exact hf.2 (e i) (e j) (he hij)
