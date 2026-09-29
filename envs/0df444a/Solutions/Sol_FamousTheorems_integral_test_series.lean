-- Prove2me | solution 1 for FamousTheorems.integral_test_series
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:17:34.304884+00:00
-- url     : https://prove2.me/submissions/aae6a318-fa62-427b-8a4e-ee151477b47d

import Mathlib

open MeasureTheory

theorem solution {f : ℝ → ℝ} {N : ℕ} (hf : AntitoneOn f (Set.Ici (N : ℝ))) (hint : IntegrableOn f (Set.Ioi (N : ℝ)))
    (hpos : ∀ t ∈ Set.Ioi (N : ℝ), 0 ≤ f t) : Summable fun n : ℕ => f n :=
  AntitoneOn.summable_of_integrableOn_Ioi hf hint hpos
