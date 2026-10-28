-- Prove2me | solution 1 for AvramDividend.Classical.chat01_continuous_martingale_nat_skeleton
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:04:42.305983+00:00
-- url     : https://prove2.me/submissions/7201f83e-15e6-478e-b82c-b90446b1b532

import Mathlib.Probability.Martingale.Basic
import Mathlib.Data.NNReal.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal

/-- Sampling a continuous-time martingale at integer times preserves its
    martingale property for the sampled filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {f : ℝ≥0 → Ω → ℝ}
    (hf : Martingale f 𝓕 μ) :
    Martingale (fun (n : ℕ) => f (n : ℝ≥0))
      ({ seq := fun (n : ℕ) => 𝓕 (n : ℝ≥0)
         mono' := by
           intro i j hij
           exact 𝓕.mono (by exact_mod_cast hij)
         le' := by
           intro i
           exact 𝓕.le (i : ℝ≥0) } : Filtration ℕ mΩ) μ := by
  constructor
  · intro n
    exact hf.1 (n : ℝ≥0)
  · intro i j hij
    exact hf.2 (i : ℝ≥0) (j : ℝ≥0) (by exact_mod_cast hij)
