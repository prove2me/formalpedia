-- Prove2me | solution 1 for AvramDividend.Classical.chat08_levy_increment_cocycle_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T09:15:40.731354+00:00
-- url     : https://prove2.me/submissions/65650469-8415-46ca-b804-267c2147e4dd

import Mathlib.Tactic.Ring
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal

/-! Split a Lévy-path increment into two adjacent deterministic increments. -/
theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (t u v : ℝ≥0) (ω : Ω) :
    Y (t + u + v) ω - Y t ω =
      (Y (t + u + v) ω - Y (t + u) ω) +
      (Y (t + u) ω - Y t ω) := by
  ring
