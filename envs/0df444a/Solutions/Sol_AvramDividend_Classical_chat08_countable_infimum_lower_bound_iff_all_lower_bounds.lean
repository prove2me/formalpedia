-- Prove2me | solution 1 for AvramDividend.Classical.chat08_countable_infimum_lower_bound_iff_all_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:26:37.644492+00:00
-- url     : https://prove2.me/submissions/276b81f2-69ca-44a7-b88f-e351704a423e

import Mathlib.Probability.Process.Stopping

open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} (τ : ℕ → Ω → WithTop ℝ≥0) (t : WithTop ℝ≥0) (ω : Ω) :
    t ≤ (⨅ k : ℕ, τ k ω) ↔ ∀ k : ℕ, t ≤ τ k ω := le_iInf_iff
