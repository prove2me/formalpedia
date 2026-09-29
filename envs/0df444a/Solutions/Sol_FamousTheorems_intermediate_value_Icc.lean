-- Prove2me | solution 1 for FamousTheorems.intermediate_value_Icc
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:47.981775+00:00
-- url     : https://prove2.me/submissions/dd871990-a755-4d10-9101-3cdd5bff3670

import Mathlib

theorem solution : ∀ {a b : ℝ}, a ≤ b → ∀ {f : ℝ → ℝ},
    ContinuousOn f (Set.Icc a b) → Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b :=
  fun hab _ hf => intermediate_value_Icc hab hf
